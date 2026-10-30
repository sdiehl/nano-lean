#!/usr/bin/env bash
# Populate benches/fixtures with the exports benches/suite.toml names.
#
#   LEAN      toolchain for the Init and Std exports (default leanprover/lean4:v4.34.1)
#   MATHLIB   a Lake project with built Mathlib oleans, for the Mathlib closures
#   CLOSURES  a directory of NAME.ndjson closures to convert when MATHLIB is unset
#   ARENA     a lean-kernel-arena tests/good/perf directory of NDJSON exports
#
# Inputs that cannot be produced are reported and skipped; the harness skips their benches.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
out=$root/benches/fixtures
LEAN=${LEAN:-leanprover/lean4:v4.34.1}
CLOSURES=${CLOSURES:-$root/.local}
ARENA=${ARENA:-$root/.local/arena-tests/good/perf}
mkdir -p "$out"

command -v olean-export >/dev/null || { echo "install olean-export: cargo install olean-export" >&2; exit 1; }
lib=$(elan run "$LEAN" lean --print-libdir)

toolchain() { # NAME MODULE [CONSTANT]
  local args=(-q -L "$lib" "$2" -f blean -o "$out/$1.blean")
  [[ $# -gt 2 ]] && args+=(-c "$3")
  olean-export "${args[@]}" && echo "$1"
}

mathlib() { # NAME CONSTANT
  if [[ -n ${MATHLIB:-} ]]; then
    (cd "$MATHLIB" && lake env olean-export -q Mathlib -c "$2" -f blean -o "$out/$1.blean") && echo "$1"
  elif [[ -f $CLOSURES/$1.ndjson ]]; then
    olean-export convert "$CLOSURES/$1.ndjson" -o "$out/$1.blean" >/dev/null && echo "$1 (converted)"
  else
    echo "skip $1: set MATHLIB or CLOSURES" >&2
  fi
}

arena() { # NAME
  if [[ -f $ARENA/$1.ndjson ]]; then
    cp "$ARENA/$1.ndjson" "$out/$1.ndjson" && echo "$1"
  else
    echo "skip $1: set ARENA" >&2
  fi
}

toolchain init Init
toolchain std Std
toolchain char-succ Init '_private.Init.Data.Char.Ordinal.0.Char.succ?_eq._proof_1_10'
toolchain int32-size Init _private.Init.Data.Range.Polymorphic.SInt.0.Int32.instRxcHasSize_eq
toolchain prev-aux Init String.Slice.Pos.prevAuxGo_le_self
toolchain week-offset Std _private.Std.Time.Date.Unit.Week.0.Std.Time.Week.Offset.ofMilliseconds._proof_1

mathlib fin-insert Fin.insertNth_apply_succAbove
mathlib rat-encodable-instance Rat.instEncodable
mathlib uniform-prod UniformOnFun.uniformEquivProdArrow._proof_1

for t in app-lam church-numerals fueled-chain grind-ring-5 let-ladder magma-list-deep-n21 \
  magma-list-pair-n7 shared-subterm shift-cascade; do
  arena "$t"
done
