#!/bin/sh
# Runs on Spark after build_and_run_spark.sh has synchronized the checkout.
set -eu
root=$1
omc=$2
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
pin=$(sed -n 's/^omc_sha256=//p' "$root/PIN")
echo "$pin  $omc" | sha256sum -c -
{ echo om2; cat "$root/src/ufbi_math.om" "$root/src/ufbi_ivmath.om" "$root/scripts/dyadic_grid_dump.om"; } > "$build/unit.om"
"$omc" < "$build/unit.om" > "$build/dump"
chmod +x "$build/dump"
"$build/dump" > "$build/omega.tsv"
{ echo om2; cat "$root/src/ufbi_math.om" "$root/src/ufbi_ivmath.om" "$root/src/ufbi_w2_dyadic.om" "$root/scripts/dyadic_w2_dump.om"; } > "$build/w2.om"
"$omc" < "$build/w2.om" > "$build/w2"
chmod +x "$build/w2"
"$build/w2" > "$build/w2-omega.tsv"
cd "${YANG_LEAN_BRIDGE:-$HOME/workspace/yang-lean-bridge}"
export PATH="$HOME/.elan/bin:$PATH"
lake env sh -ec '
  export LEAN_PATH="$1:$LEAN_PATH"
  cd "$2"
  for m in OpenAiYmBridge DobrushinShlosman WilsonPolymerBridge PhaseFourBridge OneLinkTransport DyadicTrig DyadicExp DyadicPartition DyadicPolarFlux DyadicEnergyReplay; do
    lean -DmaxHeartbeats=450000 -R proofs -o "$1/$m.olean" "proofs/$m.lean"
  done
  lean --run scripts/ReplayDyadicTrig.lean > "$1/lean.tsv"
  lean --run scripts/ReplayDyadicW2.lean > "$1/w2-lean.tsv"
' sh "$build" "$root"
cmp "$build/omega.tsv" "$build/lean.tsv"
test "$(wc -l < "$build/lean.tsv")" = 2048
sha256sum "$build/lean.tsv"
echo 'DYADIC_GRID_REPLAY cells=2048 status=PASS'
cmp "$build/w2-omega.tsv" "$build/w2-lean.tsv"
test "$(wc -l < "$build/w2-lean.tsv")" = 2048
sha256sum "$build/w2-lean.tsv"
# A one-unit change to the computed polar energy must disagree with the reference.
sed 's/^par = fluxEnergy zLo$/par = add 1 fluxEnergy zLo/' "$build/w2.om" > "$build/w2-mutant.om"
"$omc" < "$build/w2-mutant.om" > "$build/w2-mutant"
chmod +x "$build/w2-mutant"
"$build/w2-mutant" > "$build/mutant.tsv"
test "$(wc -l < "$build/mutant.tsv")" = 2048
if cmp -s "$build/mutant.tsv" "$build/w2-lean.tsv"; then
  echo 'W2_MUTATION undetected' >&2
  exit 1
fi
echo 'W2_MUTATION polar_energy_plus_one detected'
echo 'DYADIC_W2_REPLAY couplings=16 field_boxes=2048 angle_cells_per_box=2048 status=PASS'
