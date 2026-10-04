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
    # Leave 2 GiB for the 16 GiB runner's OS. The Rust exporter reads
    # the pinned oleans directly, without constructing a Lean environment.
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
    for repo in olean-export mathlib4; do
      if [[ $repo == olean-export ]]; then
        url=https://github.com/sdiehl/olean-export.git
        revision=27347bfbf2bd2433a9cb8d622566421040ce87fd
      else
        url=https://github.com/leanprover-community/mathlib4.git
        revision=d13f23b723b8a846827a245b89c10fc7d3f11612
      fi
      git init --initial-branch=main ".ci/$repo"
      git -C ".ci/$repo" remote add origin "$url"
      git -C ".ci/$repo" fetch --depth=1 origin "$revision"
      git -C ".ci/$repo" checkout --detach FETCH_HEAD
    done
    cargo build --manifest-path .ci/olean-export/Cargo.toml --release --locked -j 2
    (cd .ci/mathlib4 && elan run "$toolchain" lake exe cache get)
    exporter="$root/.ci/olean-export/target/release/tiny-olean"
    # Check a small real 4.34.1 export before generating the large artifact.
    (cd .ci/mathlib4 && elan run "$toolchain" lake env "$exporter" Init \
      -c Eq.symm -c Nat.add_comm -o "$root/.ci/export-smoke.ndjson")
    "$root/target/release/nano-lean" --export .ci/export-smoke.ndjson \
      > "$report/export-smoke.json"
    (cd .ci/mathlib4 && elan run "$toolchain" lake env "$exporter" Mathlib \
      -o "$root/.ci/mathlib.ndjson.tmp")
    mv .ci/mathlib.ndjson.tmp .ci/mathlib.ndjson
    sha256sum .ci/mathlib.ndjson > .ci/mathlib.ndjson.sha256
    rm -rf .ci/mathlib4 .ci/olean-export .ci/elan .ci/export-smoke.ndjson
    ;;
  verify)
    sha256sum --check .ci/mathlib.ndjson.sha256
    python3 - .ci/mathlib.ndjson <<'PYVERIFY'
import hashlib
import json
import sys

# Canonical name segments preserve the distinction between strings and numbers.
# The digest comes from the original pinned 4.34.1 export, independently of
# expression IDs, declaration ordering, or the exporter's JSON formatting.
names = {0: ''}
declarations = []
with open(sys.argv[1], 'rb') as source:
    metadata = json.loads(next(source))['meta']
    if (metadata['format']['version'] != '3.1.0'
            or metadata['lean']['version'] != '4.34.1'
            or metadata['lean']['githash'] != '5045d0056413266e57c625dcd7c365b10e377c52'
            or metadata['exporter']['name'] != 'tiny-olean'):
        raise SystemExit(f'Unexpected export metadata: {metadata}')
    for line in source:
        # Expressions dominate the file; decode only names and declarations.
        if not line.startswith((b'{"in":', b'{"axiom":', b'{"def":', b'{"thm":',
                                b'{"opaque":', b'{"quot":', b'{"inductive":')):
            continue
        record = json.loads(line)
        if 'in' in record:
            if 'str' in record:
                node = record['str']
                segment = json.dumps(node['str'], ensure_ascii=False)
            else:
                node = record['num']
                segment = str(node['i'])
            names[record['in']] = names[node['pre']] + '/' + segment
        for kind in ('axiom', 'def', 'thm', 'opaque', 'quot'):
            if kind in record:
                declarations.append(names[record[kind]['name']])
        if 'inductive' in record:
            for kind in ('types', 'ctors', 'recs'):
                declarations.extend(names[d['name']] for d in record['inductive'][kind])
coverage = hashlib.sha256(('\n'.join(sorted(declarations)) + '\n').encode()).hexdigest()
if len(declarations) != 718577 or coverage != 'a8e898c54b761ad374648e5b24ca25f040125409f8575a42458a37cb117e5a06':
    raise SystemExit(f'Mathlib coverage mismatch: {len(declarations)} declarations, {coverage}')
print(f'Verified Lean 4.34.1: {len(declarations)} declaration names; coverage {coverage}')
PYVERIFY
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
with open('.ci/mathlib.ndjson.sha256') as source:
    expected_digest = source.read().split()[0]
if result.get('sha256') != expected_digest:
    raise SystemExit('Checked input digest differs from the verified Mathlib export')
PY
    ;;
  *) echo "Usage: $0 prepare|verify|check" >&2; exit 2 ;;
esac
