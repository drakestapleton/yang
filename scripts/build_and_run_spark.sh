#!/bin/sh
# SPDX-License-Identifier: Apache-2.0
# Sync yang/ to Spark, compile pure seeded-OM-2 binaries with ~/canon/omega-mv/seed/out/omc,
# and run under spark-window with BOARD.md CLAIM/RELEASE discipline.
set -eu
MODE=${1:-check1}
ROOT=$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)
REMOTE_DIR="/home/drakestapleton/workspace/yang-gb10"
OMEGA_DIR="/home/drakestapleton/canon/omega-mv"

echo "=== Syncing $ROOT -> spark:$REMOTE_DIR ==="
ssh spark "mkdir -p '$REMOTE_DIR/src' '$REMOTE_DIR/proofs' '$REMOTE_DIR/build' '$REMOTE_DIR/evidence'"
COPYFILE_DISABLE=1 tar --exclude='.git' --exclude='._*' --exclude='.DS_Store' -C "$ROOT" -cf - PIN README.md src proofs scripts | ssh spark "tar -C '$REMOTE_DIR' -xf -"

if [ "$MODE" = "check1" ]; then
  echo "=== Building pure OM-2 Zero-CUDA ufbi_check1_gb10 on Spark ==="
  ssh spark "set -eu
    cd '$OMEGA_DIR'
    OMC=seed/out/omc
    {
      printf 'om2\n'
      cat \
        gpu/nvidia/native/nvrm/context.om \
        gpu/nvidia/native/blackwell/vector.om \
        gpu/nvidia/native/blackwell/launch.om \
        gpu/nvidia/native/blackwell/batch.om \
        om/encoder/bw_enc_sm121.om \
        '$REMOTE_DIR/src/ufbi_math.om' \
        '$REMOTE_DIR/src/ufbi_check1_kernels.om' \
        '$REMOTE_DIR/src/ufbi_check1_gb10.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_check1_gb10'
    chmod 755 '$REMOTE_DIR/build/ufbi_check1_gb10'
    ls -la '$REMOTE_DIR/build/ufbi_check1_gb10'
    sha256sum '$REMOTE_DIR/build/ufbi_check1_gb10'
    file '$REMOTE_DIR/build/ufbi_check1_gb10'
  "
  echo "=== Running ufbi_check1_gb10 on live GB10 under spark-window ==="
  ssh spark "set -eu
    echo \"\$(date -u +%FT%H:%MZ) CLAIM agy-yang ufbi-check1-gb10 to all: GB10 chip lock (lease 10m, --quiet none) for pure-OM-2 Zero-CUDA Check #1 4D scalar UV-divergence sweep (L=8..64)\" >> ~/handoffs/BOARD.md
    WID=\$(spark-window open ufbi-check1-gb10 --lease 10 --gb10 exclusive --quiet none | tail -n 1)
    cleanup() {
      spark-window close \"\$WID\" >/dev/null 2>&1 || true
      echo \"\$(date -u +%FT%H:%MZ) RELEASE agy-yang ufbi-check1-gb10: done, GPU idle\" >> ~/handoffs/BOARD.md
    }
    trap cleanup EXIT
    spark-window run '$REMOTE_DIR/build/ufbi_check1_gb10' > '$REMOTE_DIR/evidence/check1_gb10_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/check1_gb10_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "obs_synth" ]; then
  echo "=== Building & running pure OM-2 ufbi_obs_synth on Spark CPU ==="
  ssh spark "set -eu
    cd '$OMEGA_DIR'
    OMC=seed/out/omc
    {
      printf 'om2\n'
      cat '$REMOTE_DIR/src/ufbi_math.om' '$REMOTE_DIR/src/ufbi_obs_synth.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_obs_synth'
    chmod 755 '$REMOTE_DIR/build/ufbi_obs_synth'
    sha256sum '$REMOTE_DIR/build/ufbi_obs_synth'
    '$REMOTE_DIR/build/ufbi_obs_synth' > '$REMOTE_DIR/evidence/obs_synth_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/obs_synth_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "check3" ]; then
  echo "=== Building pure OM-2 Zero-CUDA ufbi_check3_gb10 on Spark ==="
  ssh spark "set -eu
    cd '$OMEGA_DIR'
    OMC=seed/out/omc
    {
      printf 'om2\n'
      cat \
        gpu/nvidia/native/nvrm/context.om \
        gpu/nvidia/native/blackwell/vector.om \
        gpu/nvidia/native/blackwell/launch.om \
        gpu/nvidia/native/blackwell/batch.om \
        om/encoder/bw_enc_sm121.om \
        '$REMOTE_DIR/src/ufbi_math.om' \
        '$REMOTE_DIR/src/ufbi_check3_kernels.om' \
        '$REMOTE_DIR/src/ufbi_check3_gb10.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_check3_gb10'
    chmod 755 '$REMOTE_DIR/build/ufbi_check3_gb10'
    ls -la '$REMOTE_DIR/build/ufbi_check3_gb10'
    sha256sum '$REMOTE_DIR/build/ufbi_check3_gb10'
    file '$REMOTE_DIR/build/ufbi_check3_gb10'
  "
  echo "=== Running ufbi_check3_gb10 on live GB10 under spark-window ==="
  ssh spark "set -eu
    echo \"\$(date -u +%FT%H:%MZ) CLAIM agy-yang ufbi-check3-gb10 to all: GB10 chip lock (lease 15m, --quiet none) for pure-OM-2 Zero-CUDA Check #3 4D SU(2) adversarial twisted-collar search\" >> ~/handoffs/BOARD.md
    WID=\$(spark-window open ufbi-check3-gb10 --lease 15 --gb10 exclusive --quiet none | tail -n 1)
    cleanup() {
      spark-window close \"\$WID\" >/dev/null 2>&1 || true
      echo \"\$(date -u +%FT%H:%MZ) RELEASE agy-yang ufbi-check3-gb10: done, GPU idle\" >> ~/handoffs/BOARD.md
    }
    trap cleanup EXIT
    spark-window run '$REMOTE_DIR/build/ufbi_check3_gb10' > '$REMOTE_DIR/evidence/check3_gb10_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/check3_gb10_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "obs_synth_w2" ]; then
  echo "=== Building & running pure OM-2 ufbi_obs_synth_w2 (Wave-2 Wake-Sleep + Physics Prior) on Spark CPU ==="
  ssh spark "set -eu
    cd '$OMEGA_DIR'
    OMC=seed/out/omc
    {
      printf 'om2\n'
      cat '$REMOTE_DIR/src/ufbi_math.om' '$REMOTE_DIR/src/ufbi_obs_synth_w2.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_obs_synth_w2'
    chmod 755 '$REMOTE_DIR/build/ufbi_obs_synth_w2'
    sha256sum '$REMOTE_DIR/build/ufbi_obs_synth_w2'
    '$REMOTE_DIR/build/ufbi_obs_synth_w2' > '$REMOTE_DIR/evidence/obs_synth_w2_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/obs_synth_w2_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "check4" ]; then
  echo "=== Building pure OM-2 Zero-CUDA ufbi_check4_gb10 on Spark ==="
  ssh spark "set -eu
    cd '$OMEGA_DIR'
    OMC=seed/out/omc
    {
      printf 'om2\n'
      cat \
        gpu/nvidia/native/nvrm/context.om \
        gpu/nvidia/native/blackwell/vector.om \
        gpu/nvidia/native/blackwell/launch.om \
        gpu/nvidia/native/blackwell/batch.om \
        om/encoder/bw_enc_sm121.om \
        '$REMOTE_DIR/src/ufbi_math.om' \
        '$REMOTE_DIR/src/ufbi_check3_kernels.om' \
        '$REMOTE_DIR/src/ufbi_check4_gb10.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_check4_gb10'
    chmod 755 '$REMOTE_DIR/build/ufbi_check4_gb10'
    ls -la '$REMOTE_DIR/build/ufbi_check4_gb10'
    sha256sum '$REMOTE_DIR/build/ufbi_check4_gb10'
    file '$REMOTE_DIR/build/ufbi_check4_gb10'
  "
  echo "=== Running ufbi_check4_gb10 on live GB10 under spark-window + spark-receipt ==="
  ssh spark "set -eu
    echo \"\$(date -u +%FT%H:%MZ) CLAIM agy-yang ufbi-check4-gb10 to all: GB10 chip lock (lease 15m, --quiet none) for pure-OM-2 Zero-CUDA Check #4 4D SU(2) exponential decay + 2-loop continuum scaling ladder\" >> ~/handoffs/BOARD.md
    WID=\$(spark-window open ufbi-check4-gb10 --wait --lease 15 --gb10 exclusive --quiet none | tail -n 1)
    cleanup() {
      spark-window close \"\$WID\" >/dev/null 2>&1 || true
      echo \"\$(date -u +%FT%H:%MZ) RELEASE agy-yang ufbi-check4-gb10: done, GPU idle\" >> ~/handoffs/BOARD.md
    }
    trap cleanup EXIT
    spark-window run spark-receipt ufbi-check4-gb10 --idle 5 -- sh -c '$REMOTE_DIR/build/ufbi_check4_gb10 > $REMOTE_DIR/evidence/check4_gb10_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/check4_gb10_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "obs_synth_w3" ]; then
  echo "=== Building & running pure OM-2 ufbi_obs_synth_w3 (Wave-3 INV-4 Pole-Free + Bulk-Sigma) on Spark CPU ==="
  ssh spark "set -eu
    cd '$OMEGA_DIR'
    OMC=seed/out/omc
    {
      printf 'om2\n'
      cat '$REMOTE_DIR/src/ufbi_math.om' '$REMOTE_DIR/src/ufbi_obs_synth_w3.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_obs_synth_w3'
    chmod 755 '$REMOTE_DIR/build/ufbi_obs_synth_w3'
    sha256sum '$REMOTE_DIR/build/ufbi_obs_synth_w3'
    '$REMOTE_DIR/build/ufbi_obs_synth_w3' > '$REMOTE_DIR/evidence/obs_synth_w3_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/obs_synth_w3_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "check5" ]; then
  echo "=== Building pure OM-2 Zero-CUDA ufbi_check5_gb10 on Spark ==="
  ssh spark "set -eu
    cd '$OMEGA_DIR'
    OMC=seed/out/omc
    {
      printf 'om2\n'
      cat \
        gpu/nvidia/native/nvrm/context.om \
        gpu/nvidia/native/blackwell/vector.om \
        gpu/nvidia/native/blackwell/launch.om \
        gpu/nvidia/native/blackwell/batch.om \
        om/encoder/bw_enc_sm121.om \
        '$REMOTE_DIR/src/ufbi_math.om' \
        '$REMOTE_DIR/src/ufbi_check3_kernels.om' \
        '$REMOTE_DIR/src/ufbi_check5_gb10.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_check5_gb10'
    chmod 755 '$REMOTE_DIR/build/ufbi_check5_gb10'
    ls -la '$REMOTE_DIR/build/ufbi_check5_gb10'
    sha256sum '$REMOTE_DIR/build/ufbi_check5_gb10'
    file '$REMOTE_DIR/build/ufbi_check5_gb10'
  "
  echo "=== Running ufbi_check5_gb10 on live GB10 under spark-window + spark-receipt ==="
  ssh spark "set -eu
    echo \"\$(date -u +%FT%H:%MZ) CLAIM agy-yang ufbi-check5-gb10 to all: GB10 chip lock (lease 15m, --quiet none) for pure-OM-2 Zero-CUDA Check #5 contact-free decay + physically-scaled SU(2) continuum ladder + beta=6.0 gapless control\" >> ~/handoffs/BOARD.md
    WID=\$(spark-window open ufbi-check5-gb10 --wait --lease 15 --gb10 exclusive --quiet none | tail -n 1)
    cleanup() {
      spark-window close \"\$WID\" >/dev/null 2>&1 || true
      echo \"\$(date -u +%FT%H:%MZ) RELEASE agy-yang ufbi-check5-gb10: done, GPU idle\" >> ~/handoffs/BOARD.md
    }
    trap cleanup EXIT
    spark-window run spark-receipt ufbi-check5-gb10 --idle 5 -- sh -c '$REMOTE_DIR/build/ufbi_check5_gb10 > $REMOTE_DIR/evidence/check5_gb10_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/check5_gb10_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "proofs" ]; then
  echo "=== Checking zero-dependency Lean 4 bridge proofs/UfbiMassGap.lean on Spark ==="
  ssh spark "set -eu
    ~/.elan/bin/lean --version
    ~/.elan/bin/lean '$REMOTE_DIR/proofs/UfbiMassGap.lean'
    echo 'LEAN_PROOF_CHECK status=PASS file=proofs/UfbiMassGap.lean'
  "
else
  echo "usage: $0 check1 | obs_synth | obs_synth_w2 | obs_synth_w3 | check3 | check4 | check5 | proofs" >&2
  exit 2
fi
