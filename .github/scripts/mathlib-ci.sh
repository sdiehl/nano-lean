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
  shift
  sudo systemd-run --unit="$unit" --wait --pipe --collect \
    --uid="$(id -u)" --gid="$(id -g)" \
    --working-directory="$root" \
    --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
    --setenv="GITHUB_ACTIONS=true" \
    --property=MemoryMax=11G --property=MemorySwapMax=0 \
    --property=OOMPolicy=kill \
    --property=RuntimeMaxSec=18000 \
    "$@"
}

case ${1:-} in
  prepare)
    # A cold build needs Lean, Mathlib oleans and the 5.6 GB export at once.
    available=$(df -Pk . | awk 'NR==2 {print $4}')
    if (( available < 20 * 1024 * 1024 )); then
      echo 'At least 20 GiB of free disk is required for a cold export build.' >&2
      exit 1
    fi
    bounded nano-mathlib-export bash .github/scripts/mathlib-ci.sh export \
      2>&1 | tee "$report/export.log"
    ;;
  export)
    export ELAN_HOME="$root/.ci/elan"
    curl --fail --location --retry 3 \
      https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      -o .ci/elan-init.sh
    bash .ci/elan-init.sh -y --default-toolchain none
    export PATH="$ELAN_HOME/bin:$PATH"
    toolchain=leanprover/lean4:v4.29.1
    elan toolchain install "$toolchain"
    for repo in lean4export mathlib4; do
      if [[ $repo == lean4export ]]; then
        url=https://github.com/leanprover/lean4export.git
        revision=66f1fb4bc256072069767fce52d39480e4524869
      else
        url=https://github.com/leanprover-community/mathlib4.git
        revision=5e932f97dd25535344f80f9dd8da3aab83df0fe6
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
    bounded nano-mathlib-check /usr/bin/time -v -o "$report/time.txt" \
      env NANO_LEAN_TRACE=1 NANO_LEAN_PROGRESS=1 "$root/target/release/nano-lean" \
      --export-parallel 1 --memory-mib 10240 "$root/.ci/mathlib.ndjson" \
      > "$report/result.json" \
      2> >(tee "$report/trace.jsonl" | awk '/^\[progress\]/ { print; fflush() }' >&2)
    python3 - "$report/result.json" <<'PY'
import json
import sys
with open(sys.argv[1]) as source:
    result = json.load(source)
if result.get('status') != 'checked' or result.get('declarations') != 670630:
    raise SystemExit(f'Incomplete Mathlib check: {result}')
if result.get('sha256') != 'ca2ec20fd063b61e71867b2975c81bd989af9f879b4886b8f08cd23c767a47bb':
    raise SystemExit('Checked input digest differs from the pinned Mathlib export')
PY
    ;;
  *) echo "Usage: $0 prepare|check" >&2; exit 2 ;;
esac
