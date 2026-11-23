#!/bin/sh
# Build on Spark with the pinned compiler; run each finite batch in the shared FIFO.
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
cd "$root"
out=${BLOCK_BUILD:-"$root/build/kernel"}
omega=${OMEGA_DIR:-"$HOME/canon/omega-mv"}
mode=${1:-build}
shift || true
case $mode in
build)
    mkdir -p "$out"
    pin=$(sed -n 's/^omega_mv_commit=//p' PIN)
    git -C "$omega" show "$pin:seed/out/omc" > "$out/omc"
    echo "$(sed -n 's/^omc_sha256=//p' PIN)  $out/omc" | sha256sum -c -
    chmod +x "$out/omc"
    unit="$out/kernel.om"
    echo om2 > "$unit"
    for f in gpu/nvidia/native/nvrm/context.om gpu/nvidia/native/blackwell/vector.om \
        gpu/nvidia/native/blackwell/launch.om gpu/nvidia/native/blackwell/batch.om \
        om/encoder/bw_enc_sm121.om; do git -C "$omega" show "$pin:$f" >> "$unit"; done
    cat src/ufbi_math.om src/ufbi_check3_kernels.om src/ufbi_check10_gb10.om >> "$unit"
    "$out/omc" < "$unit" > "$out/kernel"
    chmod +x "$out/kernel"
    sed 's/^fn main to int$/fn tomographyMain to int/' "$unit" > "$out/fixture.om"
    cat scripts/check_block_covariance.om >> "$out/fixture.om"
    "$out/omc" < "$out/fixture.om" > "$out/fixture"
    chmod +x "$out/fixture"
    "$out/fixture"
    sha256sum "$out/kernel" "$unit"
    ;;
batch|synthesis)
    if [ "$mode" = batch ]; then
        [ "$#" -ge 2 ] && [ $(( $# % 2 )) -eq 0 ] || exit 64
    else
        [ "$#" -eq 0 ] || exit 64
    fi
    d=$(mktemp -d "$out/batch.XXXXXX")
    post() { printf '%s %s\n' "$(date -u +%FT%TZ)" "$*" >> "$HOME/handoffs/BOARD.md"; }
    name=yang-check10-kernel
    post "REQUEST $name; finite $mode, up to 15 minutes"
    info=$(spark-window open "$name" --gb10 exclusive --quiet none --lease 15 --wait)
    wid=$(printf '%s\n' "$info" | tail -1)
    trap 'spark-window close "$wid"; post "RELEASE $name window $wid"' EXIT
    post "CLAIM $name $wid; up to 15 min; $mode $*"
    echo "$wid" > "$d/window"
    spark-window run timeout 840 sh -ec '
      mode=$1 root=$2 out=$3 d=$4; shift 4
      measure() {
         # Only reuse complete instances of this exact executable.
         for old in "$out"/batch.*/quarter-"$1"-seed-"$2".tsv; do
             if [ -f "$old" ]; then
                 cmp "$(dirname "$old")/binary.sha256" "$d/binary.sha256"
                 grep -qx "CHECK10_GB10_DONE status=PASS" "$old"
                 return
             fi
         done
         tmp=$(mktemp "$d/inflight.XXXXXX")
         "$out/kernel" "$1" "$2" > "$tmp"
         grep -qx "CHECK10_GB10_DONE status=PASS" "$tmp"
         mv "$tmp" "$d/quarter-$1-seed-$2.tsv"
      }
      sha256sum < "$out/kernel" > "$d/binary.sha256"
      if [ "$mode" = batch ]; then
          while [ "$#" -gt 0 ]; do measure "$1" "$2"; shift 2; done
      else
          for seed in 101 102 103; do for w in 0 1 2 3; do measure "$w" "$seed"; done; done
          winner=$(python3 "$root/scripts/select_block_kernel.py" "$out" --winner)
          for seed in 201 202 203 204 205 206; do
              measure 2 "$seed"
              if [ "$winner" != 2 ]; then measure "$winner" "$seed"; fi
          done
          python3 "$root/scripts/select_block_kernel.py" "$out"
      fi' sh "$mode" "$root" "$out" "$d" "$@"
    echo "$d"
    ;;
*) exit 64 ;;
esac
