#!/bin/sh
# Builds target/release/nl-fast with a profile from checking Init, an export kept as a release asset.
set -eu
cd "$(dirname "$0")"

TAG=pgo-data-1
SHA=be43e8fc8fa3f9212f6bf005a924834af5cbfdb2ec6b7524fc85efbaf5c6a76e
URL=https://github.com/sdiehl/nano-lean/releases/download/$TAG/init.ndjson.gz
FLAGS="-C target-cpu=native -C llvm-args=-align-all-functions=6"

D=target/pgo-data
GZ=$D/init.ndjson.gz
mkdir -p "$D"
sha() { (sha256sum "$1" 2>/dev/null || shasum -a 256 "$1") | cut -d' ' -f1; }
if [ ! -f "$GZ" ] || [ "$(sha "$GZ")" != "$SHA" ]; then
  curl -fsSL "$URL" -o "$GZ"
  [ "$(sha "$GZ")" = "$SHA" ] || { echo "pgo data checksum mismatch" >&2; exit 1; }
fi
[ -f "$D/init.ndjson" ] || gzip -dc "$GZ" > "$D/init.ndjson"

HOST=$(rustc -vV | sed -n 's/^host: //p')
PROFDATA=$(rustc --print sysroot)/lib/rustlib/$HOST/bin/llvm-profdata
RAW=$(mktemp -d "$D/raw.XXXXXX")

RUSTFLAGS="$FLAGS -Cprofile-generate=$PWD/$RAW" cargo build --release --locked --bin nl-fast
target/release/nl-fast -q -j 4 "$D/init.ndjson" > /dev/null
"$PROFDATA" merge -o "$RAW/merged.profdata" "$RAW"
RUSTFLAGS="$FLAGS -Cprofile-use=$PWD/$RAW/merged.profdata" cargo build --release --locked --bin nl-fast
