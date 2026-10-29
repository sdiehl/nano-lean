#!/usr/bin/env bash
set -euo pipefail

if [[ ${GITHUB_ACTIONS:-} != true || $(uname -s) != Linux ]]; then
  echo 'This script only runs on a Linux GitHub Actions runner.' >&2
  exit 1
fi

command=${1:-}
corpus=${2:-mathlib}
root=$(pwd)
scripts=$root/.github/scripts
checker=$root/target/release/nl-fast
input=$root/.ci/$corpus.ndjson
blean=$root/.ci/$corpus.blean
report=$root/.ci/$corpus-report
module=${MODULE:?}
expected_count=${DECLARATIONS:?}
toolchain=leanprover/lean4:v${LEAN_VERSION:?}
mkdir -p "$report"

pins=()
for var in MODULE LEAN_VERSION LEAN_GITHASH EXPORT_FORMAT EXPORTER_VERSION DECLARATIONS COVERAGE MATHLIB_REV; do
  pins+=(--setenv="$var=${!var:-}")
done

bounded() {
  local unit=$1 memory=$2 runtime=$3
  shift 3
  sudo systemd-run --unit="$unit" --wait --pipe --collect \
    --uid="$(id -u)" --gid="$(id -g)" --working-directory="$root" \
    --setenv="PATH=$PATH" --setenv="HOME=$HOME" --setenv=GITHUB_ACTIONS=true "${pins[@]}" \
    --property="MemoryMax=$memory" --property=MemorySwapMax=0 --property=OOMPolicy=kill \
    --property="RuntimeMaxSec=$runtime" "$@"
}

verify_input() {
  sha256sum --check "$input.sha256"
}

prepare() {
  local available
  available=$(df -Pk . | awk 'NR==2 {print $4}')
  if [[ $corpus == mathlib ]] && ((available < 20 * 1024 * 1024)); then
    echo 'At least 20 GiB of free disk is required for a cold export build.' >&2
    exit 1
  fi
  bounded nano-mathlib-export 14G 2100 \
    /usr/bin/time -v -o "$report/export-time.txt" \
    bash "$scripts/mathlib-ci.sh" export "$corpus" 2>&1 | tee "$report/export.log"
}

fetch_mathlib() {
  local rev=${MATHLIB_REV:?}
  git init --initial-branch=main .ci/mathlib4
  git -C .ci/mathlib4 remote add origin https://github.com/leanprover-community/mathlib4.git
  git -C .ci/mathlib4 fetch --depth=1 origin "$rev"
  git -C .ci/mathlib4 checkout --detach FETCH_HEAD
  if [[ $(<.ci/mathlib4/lean-toolchain) != "$toolchain" ]]; then
    echo "Mathlib $rev pins $(<.ci/mathlib4/lean-toolchain), not $toolchain" >&2
    exit 1
  fi
  (cd .ci/mathlib4 && elan run "$toolchain" lake exe cache get)
}

export_corpus() {
  export ELAN_HOME=$root/.ci/elan
  curl --fail --location --retry 3 -o .ci/elan-init.sh \
    https://raw.githubusercontent.com/leanprover/elan/v4.2.4/elan-init.sh
  bash .ci/elan-init.sh -y --default-toolchain none
  export PATH=$ELAN_HOME/bin:$PATH
  elan toolchain install "$toolchain"
  cargo install olean-export --version "=${EXPORTER_VERSION:?}" --locked -j 2 --root .ci/exporter
  local exporter=$root/.ci/exporter/bin/olean-export
  if [[ $corpus == mathlib ]]; then
    fetch_mathlib
    (cd .ci/mathlib4 && elan run "$toolchain" lake env "$exporter" Init -j 2 \
      -c Eq.symm -c Nat.add_comm -o "$root/.ci/export-smoke.ndjson")
    "$checker" .ci/export-smoke.ndjson >"$report/export-smoke.log" 2>&1
    (cd .ci/mathlib4 && elan run "$toolchain" lake env "$exporter" "$module" -j 2 -o "$input.tmp")
  else
    LEAN_PATH="$(elan run "$toolchain" lean --print-prefix)/lib/lean" \
      "$exporter" "$module" -j 2 -o "$input.tmp"
  fi
  mv "$input.tmp" "$input"
  "$exporter" convert "$input" -o "$blean.tmp"
  mv "$blean.tmp" "$blean"
  sha256sum ".ci/$corpus.ndjson" ".ci/$corpus.blean" >"$input.sha256"
  rm -rf .ci/mathlib4 .ci/exporter .ci/elan .ci/export-smoke.ndjson
}

verify() {
  verify_input
  python3 "$scripts/verify-export.py" "$input"
}

progress() {
  local elapsed last completed remaining
  while sleep 10; do
    elapsed=$((SECONDS - started))
    last=$(tail -n 1 "$report/trace.log")
    echo "[progress] checking $module; elapsed ${elapsed}s; $last"
    if [[ $last =~ ^(start|end)\ ([0-9]+)\  ]]; then
      completed=${BASH_REMATCH[2]}
      [[ ${BASH_REMATCH[1]} == end ]] && completed=$((completed + 1))
      if ((completed > 0)); then
        remaining=$((elapsed * (expected_count - completed) / completed))
        echo "[progress] $completed/$expected_count completed; estimated remaining $((remaining / 60))m $((remaining % 60))s"
      fi
    fi
    systemctl show nano-mathlib-check.service \
      --property=MemoryCurrent --property=MemoryPeak --property=CPUUsageNSec 2>/dev/null || true
  done
}

check() {
  verify_input
  local started=$SECONDS status=0 check_pid progress_pid cache=()
  # Set by workflows that restore a cache file keyed on the checker source.
  if [[ -n ${NL_CACHE:-} ]]; then cache=(--cache "$NL_CACHE"); fi
  bounded nano-mathlib-check 11G 2700 /usr/bin/time -v -o "$report/time.txt" \
    "$checker" "$input" -j 1 --trace "${cache[@]}" >"$report/failures.log" 2>"$report/trace.log" &
  check_pid=$!
  progress &
  progress_pid=$!
  trap 'kill "$progress_pid" 2>/dev/null || true' EXIT
  trap 'sudo systemctl stop nano-mathlib-check.service || true; exit 130' INT TERM
  wait "$check_pid" || status=$?
  kill "$progress_pid" && wait "$progress_pid" 2>/dev/null || true
  trap - EXIT
  cat "$report/failures.log"
  tail -n 3 "$report/trace.log"
  verify_input
  python3 "$scripts/check-report.py" "$report" "$status" "$input.sha256"
}

check_blean() {
  verify_input
  local status=0 summary
  bounded nano-mathlib-blean 11G 1200 /usr/bin/time -v -o "$report/blean-time.txt" \
    "$checker" "$blean" -j "$(nproc)" >"$report/blean-failures.log" 2>"$report/blean.log" || status=$?
  cat "$report/blean-failures.log"
  tail -n 2 "$report/blean.log"
  summary=$(grep -E '^experimental checks ' "$report/blean.log" || true)
  if ((status != 0)) || [[ -s $report/blean-failures.log ]] ||
    [[ ! $summary =~ :\ $expected_count\ attempted,\ 0\ failures,\ 0\ fallbacks$ ]]; then
    echo "Blean check failed: exit $status, $summary" >&2
    exit 1
  fi
}

case $command in
  prepare) prepare ;;
  export) export_corpus ;;
  verify) verify ;;
  check) check ;;
  check-blean) check_blean ;;
  *)
    echo "Usage: $0 prepare|verify|check|check-blean [mathlib|init-prelude|init|std]" >&2
    exit 2
    ;;
esac
