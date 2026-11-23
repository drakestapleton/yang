#!/bin/sh
# On Spark, from an isolated Yang checkout. build only uses the host.
set -eu
root=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
cd "$root"
omega=${OMEGA_DIR:-"$HOME/canon/omega-mv"}
out=${SPECTRUM_BUILD:-"$root/build/spectrum"}
mkdir -p "$out"
case "${1:-}" in
build)
    pin=$(sed -n 's/^omega_mv_commit=//p' PIN)
    hash=$(sed -n 's/^omc_sha256=//p' PIN)
    git -C "$omega" show "$pin:seed/out/omc" > "$out/omc"
    echo "$hash  $out/omc" | sha256sum -c -
    chmod +x "$out/omc"
    unit="$out/spectrum.om"
    echo om2 > "$unit"
    for f in gpu/nvidia/native/nvrm/context.om gpu/nvidia/native/blackwell/vector.om \
        gpu/nvidia/native/blackwell/launch.om gpu/nvidia/native/blackwell/batch.om \
        om/encoder/bw_enc_sm121.om; do
        git -C "$omega" show "$pin:$f" >> "$unit"
    done
    cat src/ufbi_math.om src/ufbi_check3_kernels.om src/wilson_gb10.om >> "$unit"
    cp "$unit" "$out/check3.om"
    cat src/ufbi_check3_gb10.om >> "$out/check3.om"
    "$out/omc" < "$out/check3.om" > "$out/check3"
    cat src/plaquette_spectrum.om >> "$unit"
    "$out/omc" < "$unit" > "$out/spectrum.new"
    chmod +x "$out/spectrum.new"
    "$out/spectrum.new"
    mv "$out/spectrum.new" "$out/spectrum"
    sha256sum "$out/spectrum" "$unit"
    ;;
run|batch)
    mode=$1
    shift
    if [ "$mode" = run ]; then
        [ "$#" -eq 5 ] || { echo 'run T chain burn observations inner-sweeps' >&2; exit 64; }
        T=$1 chain=$2 burn=$3 count=$4 inner=$5
        set -- "$T" "$chain"
    else
        # An explicit list of T,chain pairs shares one FIFO ticket and one deadline.
        [ "$#" -ge 5 ] && [ $((($#-3)%2)) -eq 0 ] || {
            echo 'batch burn observations inner-sweeps T chain [T chain ...]' >&2; exit 64;
        }
        burn=$1 count=$2 inner=$3
        shift 3
    fi
    name=yang-plaquette-$1-$2
    board="$HOME/handoffs/BOARD.md"
    post() { flock "$board.lock" sh -c 'echo "$1" >> "$2"' sh "$(date -u +%FT%TZ) $1" "$board"; }
    post "QUEUE $name exclusive GB10, value measurements, lease 20m; contact via board"
    info=$(spark-window open "$name" --gb10 exclusive --quiet none --lease 20 --wait)
    wid=$(echo "$info" | tail -1)
    cleanup() { spark-window close "$wid"; post "RELEASE $name window $wid"; }
    trap cleanup EXIT
    post "CLAIM $name $wid; $mode, extent/chain pairs $*"
    # The group deadline fits inside the hardware lease. A partial chain has no END.
    spark-window run timeout 1100 sh -eu -c '
        out=$1 burn=$2 count=$3 inner=$4
        shift 4
        while [ "$#" -gt 0 ]; do
            raw=$(mktemp "$out/chain-$1-$2.XXXXXX")
            "$out/spectrum" "$1" "$2" "$burn" "$count" "$inner" > "$raw"
            test "$(tail -1 "$raw")" = END
            echo "raw=$raw"
            shift 2
        done
    ' sh "$out" "$burn" "$count" "$inner" "$@"
    ;;
*) echo 'usage: build | run T chain burn observations inner | batch burn observations inner T chain [T chain ...]' >&2; exit 64 ;;
esac
