#!/usr/bin/env bash
set -euo pipefail

# Large inputs belong on the disposable Linux CI runner, not the developer host.
if [[ ${GITHUB_ACTIONS:-} != true || $(uname -s) != Linux ]]; then
  echo 'This script only runs on a Linux GitHub Actions runner.' >&2
  exit 1
fi

root=$(pwd)
corpus=${2:-mathlib}
# The workflow matrix supplies every pin.
module=${MODULE:?}
lean_version=${LEAN_VERSION:?}
lean_githash=${LEAN_GITHASH:?}
format_version=${EXPORT_FORMAT:?}
exporter_version=${EXPORTER_VERSION:?}
expected_count=${DECLARATIONS:?}
expected_coverage=${COVERAGE:?}
mathlib_rev=${MATHLIB_REV:-}
input="$root/.ci/$corpus.ndjson"
blean="$root/.ci/$corpus.blean"
report="$root/.ci/$corpus-report"
mkdir -p "$report"
pins=()
for var in MODULE LEAN_VERSION LEAN_GITHASH EXPORT_FORMAT EXPORTER_VERSION DECLARATIONS COVERAGE \
  MATHLIB_REV; do
  pins+=(--setenv="$var=${!var:-}")
done

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
    --setenv="GITHUB_ACTIONS=true" "${pins[@]}" \
    --property="MemoryMax=$memory" --property=MemorySwapMax=0 \
    --property=OOMPolicy=kill \
    --property="RuntimeMaxSec=$runtime" \
    "$@"
}

case ${1:-} in
  prepare)
    # A cold build needs Lean, Mathlib oleans and the 6.2 GB export at once.
    available=$(df -Pk . | awk 'NR==2 {print $4}')
    if [[ $corpus == mathlib ]] && (( available < 20 * 1024 * 1024 )); then
      echo 'At least 20 GiB of free disk is required for a cold export build.' >&2
      exit 1
    fi
    # Leave 2 GiB for the 16 GiB runner's OS. The Rust exporter reads
    # the pinned oleans directly, without constructing a Lean environment.
    # Bound the service itself too: a step timeout does not stop systemd units.
    bounded nano-mathlib-export 14G 2100 \
      /usr/bin/time -v -o "$report/export-time.txt" \
      bash .github/scripts/mathlib-ci.sh export "$corpus" \
      2>&1 | tee "$report/export.log"
    ;;
  export)
    export ELAN_HOME="$root/.ci/elan"
    curl --fail --location --retry 3 \
      https://raw.githubusercontent.com/leanprover/elan/v4.2.4/elan-init.sh \
      -o .ci/elan-init.sh
    bash .ci/elan-init.sh -y --default-toolchain none
    export PATH="$ELAN_HOME/bin:$PATH"
    toolchain=leanprover/lean4:v$lean_version
    elan toolchain install "$toolchain"
    cargo install olean-export --version "=$exporter_version" --locked -j 2 --root "$root/.ci/exporter"
    if [[ $corpus == mathlib ]]; then
      git init --initial-branch=main .ci/mathlib4
      git -C .ci/mathlib4 remote add origin https://github.com/leanprover-community/mathlib4.git
      git -C .ci/mathlib4 fetch --depth=1 origin "$mathlib_rev"
      git -C .ci/mathlib4 checkout --detach FETCH_HEAD
      if [[ $(< .ci/mathlib4/lean-toolchain) != "$toolchain" ]]; then
        echo "Mathlib $mathlib_rev pins $(< .ci/mathlib4/lean-toolchain), not $toolchain" >&2
        exit 1
      fi
      (cd .ci/mathlib4 && elan run "$toolchain" lake exe cache get)
    fi
    exporter="$root/.ci/exporter/bin/olean-export"
    if [[ $corpus == mathlib ]]; then
      # Check a small real export before generating the large artifact.
      (cd .ci/mathlib4 && elan run "$toolchain" lake env "$exporter" Init -j 2 \
        -c Eq.symm -c Nat.add_comm -o "$root/.ci/export-smoke.ndjson")
      "$root/target/release/nl-fast" .ci/export-smoke.ndjson \
        > "$report/export-smoke.log" 2>&1
      (cd .ci/mathlib4 && elan run "$toolchain" lake env "$exporter" "$module" -j 2 \
        -o "$input.tmp")
    else
      LEAN_PATH="$(elan run "$toolchain" lean --print-prefix)/lib/lean" \
        "$exporter" "$module" -j 2 -o "$input.tmp"
    fi
    mv "$input.tmp" "$input"
    "$exporter" convert "$input" -o "$blean.tmp"
    mv "$blean.tmp" "$blean"
    (cd "$root" && sha256sum ".ci/$corpus.ndjson" ".ci/$corpus.blean" > "$input.sha256")
    rm -rf .ci/mathlib4 .ci/exporter .ci/elan .ci/export-smoke.ndjson
    ;;
  verify)
    sha256sum --check "$input.sha256"
    python3 - "$input" "$expected_count" "$expected_coverage" "$lean_version" "$lean_githash" \
      "$format_version" "$exporter_version" <<'PYVERIFY'
import hashlib
import json
import sys

# Canonical name segments preserve the distinction between strings and numbers.
# Coverage pins identify the complete declaration set independently of
# expression IDs, declaration ordering, or the exporter's JSON formatting.
names = {0: ''}
declarations = []
with open(sys.argv[1], 'rb') as source:
    metadata = json.loads(next(source))['meta']
    lean, githash, fmt, exporter = sys.argv[4:8]
    if (metadata['format']['version'] != fmt
            or metadata['lean']['version'] != lean
            or metadata['lean']['githash'] != githash
            or metadata['exporter']['name'] != 'olean-export'
            or metadata['exporter']['version'] != exporter):
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
if len(declarations) != int(sys.argv[2]) or coverage != sys.argv[3]:
    raise SystemExit(f'Export coverage mismatch: {len(declarations)} declarations, {coverage}')
print(f'Verified Lean {lean}: {len(declarations)} declaration names; coverage {coverage}')
PYVERIFY
    ;;
  check)
    # Keep the complete declaration trace; Actions gets a heartbeat every 10s,
    # including during import or a single unusually expensive declaration.
    sha256sum --check "$input.sha256"
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
      "$root/target/release/nl-fast" "$input" -j 1 --trace \
      > "$report/failures.log" 2> "$report/trace.log" &
    check_pid=$!
    progress() {
      while sleep 10; do
        elapsed=$((SECONDS - started))
        last=$(tail -n 1 "$report/trace.log")
        echo "[progress] checking $module; elapsed ${elapsed}s; $last"
        if [[ $last =~ ^(start|end)\ ([0-9]+)\  ]]; then
          completed=${BASH_REMATCH[2]}
          if [[ ${BASH_REMATCH[1]} == end ]]; then
            completed=$((completed + 1))
          fi
          if (( completed > 0 )); then
            remaining=$((elapsed * (expected_count - completed) / completed))
            echo "[progress] ${completed}/${expected_count} completed; estimated remaining $((remaining / 60))m $((remaining % 60))s"
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
    sha256sum --check "$input.sha256"
    python3 - "$report" "$status" "$expected_count" "$input.sha256" <<'PYRESULT'
import json
import re
import sys
from decimal import Decimal, InvalidOperation
from pathlib import Path

report = Path(sys.argv[1])
status = int(sys.argv[2])
expected_count = int(sys.argv[3])
completed = 0
pending = None
summary = None
error = None
timing = {}
units = {'ns': 1e-9, 'µs': 1e-6, 'us': 1e-6, 'ms': 1e-3, 's': 1.0}
def seconds(text):
    match = re.fullmatch(r'([0-9.]+)(ns|µs|us|ms|s)', text)
    return float(match.group(1)) * units[match.group(2)] if match else None
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
        elif line.startswith('import '):
            value = seconds(line.split()[1])
            if value is not None:
                timing['import_seconds'] = value
        elif line.startswith('experimental checks '):
            match = re.fullmatch(
                r'experimental checks (.+): (\d+) attempted, (\d+) failures, (\d+) fallbacks\n?', line)
            if match:
                summary = dict(zip(('attempted', 'failures', 'fallbacks'),
                                   map(int, match.groups()[1:])))
                value = seconds(match.group(1))
                if value is not None:
                    timing['check_seconds'] = value
if (status != 0 or completed != expected_count or pending is not None
        or summary != {'attempted': expected_count, 'failures': 0, 'fallbacks': 0}
        or (report / 'failures.log').stat().st_size):
    error = error or 'Incomplete or unsuccessful corpus check'
result = {
    'status': 'failed' if error else 'checked',
    'declarations': completed,
    'exit_code': status,
    'sha256': Path(sys.argv[4]).read_text().split()[0],
    **(summary or {}),
}
if error:
    result['error'] = error
time_file = report / 'time.txt'
if time_file.exists():
    for line in time_file.read_text().splitlines():
        if 'Elapsed (wall clock) time' in line:
            seconds = 0.0
            for part in line.rsplit(' ', 1)[1].split(':'):
                seconds = seconds * 60 + float(part)
            timing['wall_seconds'] = seconds
result.update(timing)
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
                # Never give an incomplete check a complete-corpus score.
                'virtual_cpu_seconds': None if error else instructions / 6_000_000_000,
                'virtual_cpu_minutes': None if error else instructions / 360_000_000_000,
            }
        except (ValueError, KeyError, InvalidOperation, OverflowError):
            continue
(report / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
def duration(value):
    return f'{int(value // 60)}m {value % 60:.1f}s' if value >= 60 else f'{value:.2f}s'
rows = [('Status', result['status']), ('Declarations', f"{result['declarations']:,}")]
if summary:
    rows.append(('Checked', f"{summary['attempted']:,} attempted, {summary['failures']:,} failures, "
                            f"{summary['fallbacks']:,} fallbacks"))
for key, label in (('wall_seconds', 'Wall time'), ('import_seconds', 'Import'),
                   ('check_seconds', 'Check')):
    if key in timing:
        rows.append((label, duration(timing[key])))
measurement = result['instruction_measurement']
if 'instructions' in measurement:
    rows.append(('Instructions', f"{measurement['instructions'] / 1e12:.3f}T ({measurement['status']})"))
else:
    rows.append(('Instructions', measurement['status']))
rows += [('Exit code', str(status)), ('Export SHA-256', result['sha256'])]
if error:
    rows.append(('Error', error))
text = '\n'.join(f'{label:<16}{value}' for label, value in rows) + '\n'
(report / 'summary.txt').write_text(text)
print(text, end='')
if 'wall_seconds' in timing:
    line = f"Wall time {duration(timing['wall_seconds'])}"
    if 'import_seconds' in timing and 'check_seconds' in timing:
        line += f" (import {timing['import_seconds']:.1f}s, check {timing['check_seconds']:.1f}s)"
    (report / 'wall.txt').write_text(line + '\n')
if error:
    raise SystemExit(1)
PYRESULT
    ;;
  check-blean)
    # The same export through the memory-mapped binary loader, on every core.
    sha256sum --check "$input.sha256"
    status=0
    bounded nano-mathlib-blean 11G 1200 /usr/bin/time -v -o "$report/blean-time.txt" \
      "$root/target/release/nl-fast" "$blean" -j "$(nproc)" \
      > "$report/blean-failures.log" 2> "$report/blean.log" || status=$?
    cat "$report/blean-failures.log"
    tail -n 2 "$report/blean.log"
    summary=$(grep -E '^experimental checks ' "$report/blean.log" || true)
    if (( status != 0 )) || [[ -s $report/blean-failures.log ]] \
      || [[ ! $summary =~ :\ $expected_count\ attempted,\ 0\ failures,\ 0\ fallbacks$ ]]; then
      echo "Blean check failed: exit $status, $summary" >&2
      exit 1
    fi
    ;;
  *) echo "Usage: $0 prepare|verify|check|check-blean [mathlib|init-prelude|init|std]" >&2; exit 2 ;;
esac
