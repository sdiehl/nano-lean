#!/usr/bin/env bash
set -euo pipefail

# Large inputs belong on the disposable Linux CI runner, not the developer host.
if [[ ${GITHUB_ACTIONS:-} != true || $(uname -s) != Linux ]]; then
  echo 'This script only runs on a Linux GitHub Actions runner.' >&2
  exit 1
fi

root=$(pwd)
report="$root/.ci/mathlib-report"
mkdir -p "$report"

# Limit the whole process tree, including compressed/swap-backed allocations.
# Swap is disabled for this cgroup; OOM terminates the group instead of siblings
# in an unrelated CI job. MemoryMax also accounts for reclaimable file cache.
bounded() {
  local unit=$1
  local memory=$2
  local runtime=$3
  shift 3
  sudo systemd-run --unit="$unit" --wait --pipe --collect \
    --uid="$(id -u)" --gid="$(id -g)" \
    --working-directory="$root" \
    --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
    --setenv="GITHUB_ACTIONS=true" \
    --property="MemoryMax=$memory" --property=MemorySwapMax=0 \
    --property=OOMPolicy=kill \
    --property="RuntimeMaxSec=$runtime" \
    "$@"
}

case ${1:-} in
  prepare)
    # A cold build needs Lean, Mathlib oleans and the 6.2 GB export at once.
    available=$(df -Pk . | awk 'NR==2 {print $4}')
    if (( available < 20 * 1024 * 1024 )); then
      echo 'At least 20 GiB of free disk is required for a cold export build.' >&2
      exit 1
    fi
    # The exporter retains the imported Lean environment and its deduplication
    # tables. The checker's 11 GiB cap can make it repeatedly fault mapped oleans
    # back in near the end of Mathlib. Leave 2 GiB for the 16 GiB runner's OS.
    # Bound the service itself too: a step timeout does not stop systemd units.
    bounded nano-mathlib-export 14G 2100 \
      /usr/bin/time -v -o "$report/export-time.txt" \
      bash .github/scripts/mathlib-ci.sh export \
      2>&1 | tee "$report/export.log"
    ;;
  export)
    export ELAN_HOME="$root/.ci/elan"
    curl --fail --location --retry 3 \
      https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      -o .ci/elan-init.sh
    bash .ci/elan-init.sh -y --default-toolchain none
    export PATH="$ELAN_HOME/bin:$PATH"
    toolchain=leanprover/lean4:v4.34.1
    elan toolchain install "$toolchain"
    for repo in lean4export mathlib4; do
      if [[ $repo == lean4export ]]; then
        url=https://github.com/leanprover/lean4export.git
        revision=66f1fb4bc256072069767fce52d39480e4524869
      else
        url=https://github.com/leanprover-community/mathlib4.git
        revision=d13f23b723b8a846827a245b89c10fc7d3f11612
      fi
      git init ".ci/$repo"
      git -C ".ci/$repo" remote add origin "$url"
      git -C ".ci/$repo" fetch --depth=1 origin "$revision"
      git -C ".ci/$repo" checkout --detach FETCH_HEAD
    done
    (cd .ci/lean4export && elan run "$toolchain" lake build)
    (cd .ci/mathlib4 && elan run "$toolchain" lake exe cache get)
    (cd .ci/mathlib4 && elan run "$toolchain" lake env \
      ../lean4export/.lake/build/bin/lean4export Mathlib) > .ci/mathlib.ndjson.tmp
    mv .ci/mathlib.ndjson.tmp .ci/mathlib.ndjson
    rm -rf .ci/mathlib4 .ci/lean4export .ci/elan
    ;;
  check)
    # Show periodic Rust progress in Actions and retain the full trace artifact.
    bounded nano-mathlib-check 11G 18000 /usr/bin/time -v -o "$report/time.txt" \
      env NANO_LEAN_TRACE=1 NANO_LEAN_PROGRESS=1 "$root/target/release/nano-lean" \
      --export-parallel 1 --memory-mib 10240 "$root/.ci/mathlib.ndjson" \
      > "$report/result.json" \
      2> >(tee "$report/trace.jsonl" | awk '/^\[progress\]/ { print; fflush() }' >&2)
    python3 - "$report/result.json" <<'PY'
import json
import sys
with open(sys.argv[1]) as source:
    result = json.load(source)
if result.get('status') != 'checked' or result.get('declarations') != 718577:
    raise SystemExit(f'Incomplete Mathlib check: {result}')
if result.get('sha256') != '22c5de83469408950005589a3bc5ef5157c65549b5a802f85d567c29151306a6':
    raise SystemExit('Checked input digest differs from the pinned Mathlib export')
PY
    ;;
  *) echo "Usage: $0 prepare|check" >&2; exit 2 ;;
esac
