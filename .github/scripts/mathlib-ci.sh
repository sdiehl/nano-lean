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
    git init --initial-branch=main .ci/mathlib4
    git -C .ci/mathlib4 remote add origin https://github.com/leanprover-community/mathlib4.git
    git -C .ci/mathlib4 fetch --depth=1 origin d13f23b723b8a846827a245b89c10fc7d3f11612
    git -C .ci/mathlib4 checkout --detach FETCH_HEAD
    cargo install olean-export --version '=0.1.0' --locked -j 2 --root "$root/.ci/exporter"
    (cd .ci/mathlib4 && elan run "$toolchain" lake exe cache get)
    exporter="$root/.ci/exporter/bin/olean-export"
    # Check a small real 4.34.1 export before generating the large artifact.
    (cd .ci/mathlib4 && elan run "$toolchain" lake env "$exporter" Init -j 2 \
      -c Eq.symm -c Nat.add_comm -o "$root/.ci/export-smoke.ndjson")
    "$root/target/release/examples/nl" .ci/export-smoke.ndjson 1 \
      --native-only --steps 100000000 --arena-mib 256 \
      > "$report/export-smoke.log" 2>&1
    (cd .ci/mathlib4 && elan run "$toolchain" lake env "$exporter" Mathlib -j 2 \
      -o "$root/.ci/mathlib.ndjson.tmp")
    mv .ci/mathlib.ndjson.tmp .ci/mathlib.ndjson
    sha256sum .ci/mathlib.ndjson > .ci/mathlib.ndjson.sha256
    rm -rf .ci/mathlib4 .ci/exporter .ci/elan .ci/export-smoke.ndjson
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
            or metadata['exporter']['name'] != 'olean-export'
            or metadata['exporter']['version'] != '0.1.0'):
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
    # Keep the complete declaration trace; Actions gets a heartbeat every 10s,
    # including during import or a single unusually expensive declaration.
    sha256sum --check .ci/mathlib.ndjson.sha256
    # Probe inside the same service/user context as the checker. Installing perf
    # or changing permissions cannot supply a PMU hidden by the hypervisor.
    perf_command=()
    echo 'Instruction counting unavailable: no working hardware counter.' > "$report/perf-status.txt"
    for perf_binary in /usr/lib/linux-tools/*/perf; do
      [[ -x $perf_binary ]] || continue
      for event in instructions instructions:u; do
        if bounded nano-mathlib-perf-probe 256M 15 \
          "$perf_binary" stat -j -o "$report/perf-probe.jsonl" -e "$event" -- \
          python3 -c 'sum(range(100000))' 2>> "$report/perf-probe.log" \
          && python3 - "$report/perf-probe.jsonl" <<'PYPROBE'
import json
import sys
from decimal import Decimal, InvalidOperation
with open(sys.argv[1]) as source:
    for line in source:
        try:
            row = json.loads(line)
            if (row.get('event', '').split(':')[0] == 'instructions'
                    and Decimal(row['counter-value']) > 0):
                raise SystemExit(0)
        except (ValueError, KeyError, InvalidOperation):
            pass
raise SystemExit(1)
PYPROBE
        then
          perf_command=("$perf_binary" stat -j -o "$report/perf.jsonl"
            -e duration_time -e task-clock -e "$event" --)
          echo "Instruction counting enabled: $event; $(uname -m); $($perf_binary --version)" > "$report/perf-status.txt"
          break 2
        fi
      done
    done
    cat "$report/perf-status.txt"
    started=$SECONDS
    bounded nano-mathlib-check 11G 2700 "${perf_command[@]}" /usr/bin/time -v -o "$report/time.txt" \
      "$root/target/release/examples/nl" "$root/.ci/mathlib.ndjson" 1 \
      --native-only --trace --steps 100000000 --arena-mib 256 \
      > "$report/failures.log" 2> "$report/trace.log" &
    check_pid=$!
    progress() {
      while sleep 10; do
        elapsed=$((SECONDS - started))
        last=$(tail -n 1 "$report/trace.log")
        echo "[progress] checking Mathlib; elapsed ${elapsed}s; $last"
        if [[ $last =~ ^(start|end)\ ([0-9]+)\  ]]; then
          completed=${BASH_REMATCH[2]}
          if [[ ${BASH_REMATCH[1]} == end ]]; then
            completed=$((completed + 1))
          fi
          if (( completed > 0 )); then
            echo "[progress] ${completed}/718577 completed; estimated remaining $((elapsed * (718577 - completed) / completed))s"
          fi
        fi
        systemctl show nano-mathlib-check.service \
          --property=MemoryCurrent --property=MemoryPeak --property=CPUUsageNSec \
          2>/dev/null || true
      done
    }
    progress &
    progress_pid=$!
    trap 'kill "$progress_pid" 2>/dev/null || true; wait "$progress_pid" 2>/dev/null || true' EXIT
    trap 'sudo systemctl stop nano-mathlib-check.service || true; exit 130' INT TERM
    status=0
    wait "$check_pid" || status=$?
    kill "$progress_pid" 2>/dev/null || true
    wait "$progress_pid" 2>/dev/null || true
    trap - EXIT
    cat "$report/failures.log"
    tail -n 3 "$report/trace.log"
    # Check the same pinned bytes after execution, before accepting the result.
    sha256sum --check .ci/mathlib.ndjson.sha256
    python3 - "$report" "$status" <<'PYRESULT'
import json
import re
import sys
from decimal import Decimal, InvalidOperation
from pathlib import Path

report = Path(sys.argv[1])
status = int(sys.argv[2])
completed = 0
pending = None
summary = None
error = None
with (report / 'trace.log').open() as source:
    for line in source:
        if line.startswith('start '):
            index = int(line.split()[1])
            if pending is not None or index != completed:
                error = 'Missing, repeated or out-of-order declaration start'
            pending = index
        elif line.startswith('end '):
            index = int(line.split()[1])
            if pending != index or index != completed:
                error = 'Missing, repeated or out-of-order declaration completion'
            pending = None
            completed += 1
        elif line.startswith('experimental checks '):
            match = re.fullmatch(
                r'experimental checks (.+): (\d+) attempted, (\d+) failures, (\d+) fallbacks\n?', line)
            if match:
                summary = dict(zip(('attempted', 'failures', 'fallbacks'),
                                   map(int, match.groups()[1:])))
if (status != 0 or completed != 718577 or pending is not None
        or summary != {'attempted': 718577, 'failures': 0, 'fallbacks': 0}
        or (report / 'failures.log').stat().st_size):
    error = error or 'Incomplete or unsuccessful Mathlib check'
result = {
    'status': 'failed' if error else 'checked',
    'declarations': completed,
    'exit_code': status,
    'sha256': Path('.ci/mathlib.ndjson.sha256').read_text().split()[0],
    **(summary or {}),
}
if error:
    result['error'] = error
result['instruction_measurement'] = {'status': 'unavailable'}
perf_file = report / 'perf.jsonl'
if perf_file.exists():
    for line in perf_file.read_text().splitlines():
        try:
            row = json.loads(line)
            if row.get('event', '').split(':')[0] != 'instructions':
                continue
            instructions = int(Decimal(row['counter-value']))
            coverage = float(row['pcnt-running'])
            if instructions <= 0 or not 99.9 <= coverage <= 100.0:
                continue
            result['instruction_measurement'] = {
                'status': 'partial' if error else 'measured',
                'event': row['event'],
                'instructions': instructions,
                'counter_running_percent': coverage,
                # Never give an incomplete check a full-Mathlib score.
                'virtual_cpu_seconds': None if error else instructions / 6_000_000_000,
                'virtual_cpu_minutes': None if error else instructions / 360_000_000_000,
            }
        except (ValueError, KeyError, InvalidOperation, OverflowError):
            continue
(report / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
if error:
    raise SystemExit(1)
PYRESULT
    ;;
  *) echo "Usage: $0 prepare|verify|check" >&2; exit 2 ;;
esac
