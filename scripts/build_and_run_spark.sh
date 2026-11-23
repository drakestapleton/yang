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

case "$MODE" in
  interval_cert|phase3b_cert|phase4_cert)
    pin=$(sed -n 's/^omc_sha256=//p' "$ROOT/PIN")
    ssh spark "echo '$pin  $OMEGA_DIR/seed/out/omc' | sha256sum -c -"
    ;;
esac

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
elif [ "$MODE" = "check6" ]; then
  echo "=== Building pure OM-2 Zero-CUDA ufbi_check6_gb10 on Spark ==="
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
        '$REMOTE_DIR/src/ufbi_check6_gb10.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_check6_gb10'
    chmod 755 '$REMOTE_DIR/build/ufbi_check6_gb10'
    ls -la '$REMOTE_DIR/build/ufbi_check6_gb10'
    sha256sum '$REMOTE_DIR/build/ufbi_check6_gb10'
    file '$REMOTE_DIR/build/ufbi_check6_gb10'
  "
  echo "=== Running ufbi_check6_gb10 on live GB10 under spark-window + spark-receipt ==="
  ssh spark "set -eu
    echo \"\$(date -u +%FT%H:%MZ) CLAIM agy-yang ufbi-check6-gb10 to all: GB10 chip lock (lease 15m, --quiet none) for pure-OM-2 Zero-CUDA Check #6 high-stats 512-sweep 3-point scaled continuum ladder L=8,12,16 + beta=6.0 control + scaled Wave-3 observable\" >> ~/handoffs/BOARD.md
    WID=\$(spark-window open ufbi-check6-gb10 --wait --lease 15 --gb10 exclusive --quiet none | tail -n 1)
    cleanup() {
      spark-window close \"\$WID\" >/dev/null 2>&1 || true
      echo \"\$(date -u +%FT%H:%MZ) RELEASE agy-yang ufbi-check6-gb10: done, GPU idle\" >> ~/handoffs/BOARD.md
    }
    trap cleanup EXIT
    spark-window run spark-receipt ufbi-check6-gb10 --idle 5 -- sh -c '$REMOTE_DIR/build/ufbi_check6_gb10 > $REMOTE_DIR/evidence/check6_gb10_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/check6_gb10_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "check7" ]; then
  echo "=== Building pure OM-2 Zero-CUDA ufbi_check7_gb10 on Spark ==="
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
        '$REMOTE_DIR/src/ufbi_check7_gb10.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_check7_gb10'
    chmod 755 '$REMOTE_DIR/build/ufbi_check7_gb10'
    ls -la '$REMOTE_DIR/build/ufbi_check7_gb10'
    sha256sum '$REMOTE_DIR/build/ufbi_check7_gb10'
    file '$REMOTE_DIR/build/ufbi_check7_gb10'
  "
  echo "=== Running ufbi_check7_gb10 on live GB10 under spark-window + spark-receipt ==="
  ssh spark "set -eu
    echo \"\$(date -u +%FT%H:%MZ) CLAIM agy-yang ufbi-check7-gb10 to all: GB10 chip lock (lease 15m, --quiet none) for pure-OM-2 Zero-CUDA Check #7 smooth k=0 IR collars + UV-regular Wave-3 observable\" >> ~/handoffs/BOARD.md
    WID=\$(spark-window open ufbi-check7-gb10 --wait --lease 15 --gb10 exclusive --quiet none | tail -n 1)
    cleanup() {
      spark-window close \"\$WID\" >/dev/null 2>&1 || true
      echo \"\$(date -u +%FT%H:%MZ) RELEASE agy-yang ufbi-check7-gb10: done, GPU idle\" >> ~/handoffs/BOARD.md
    }
    trap cleanup EXIT
    spark-window run spark-receipt ufbi-check7-gb10 --idle 5 -- sh -c '$REMOTE_DIR/build/ufbi_check7_gb10 > $REMOTE_DIR/evidence/check7_gb10_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/check7_gb10_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "check8" ]; then
  echo "=== Building pure OM-2 Zero-CUDA ufbi_check8_gb10 on Spark ==="
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
        '$REMOTE_DIR/src/ufbi_check8_gb10.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_check8_gb10'
    chmod 755 '$REMOTE_DIR/build/ufbi_check8_gb10'
    ls -la '$REMOTE_DIR/build/ufbi_check8_gb10'
    sha256sum '$REMOTE_DIR/build/ufbi_check8_gb10'
    file '$REMOTE_DIR/build/ufbi_check8_gb10'
  "
  echo "=== Running ufbi_check8_gb10 on live GB10 under spark-window + spark-receipt ==="
  ssh spark "set -eu
    echo \"\$(date -u +%FT%H:%MZ) CLAIM agy-yang ufbi-check8-gb10 to all: GB10 chip lock (lease 15m, --quiet none) for pure-OM-2 Zero-CUDA Check #8 Phase-II multi-scale gauge-covariant block-spin RG flow (16^4 -> 8^4 -> 4^4)\" >> ~/handoffs/BOARD.md
    WID=\$(spark-window open ufbi-check8-gb10 --wait --lease 15 --gb10 exclusive --quiet none | tail -n 1)
    cleanup() {
      spark-window close \"\$WID\" >/dev/null 2>&1 || true
      echo \"\$(date -u +%FT%H:%MZ) RELEASE agy-yang ufbi-check8-gb10: done, GPU idle\" >> ~/handoffs/BOARD.md
    }
    trap cleanup EXIT
    spark-window run spark-receipt ufbi-check8-gb10 --idle 5 -- sh -c '$REMOTE_DIR/build/ufbi_check8_gb10 > $REMOTE_DIR/evidence/check8_gb10_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/check8_gb10_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "check9" ]; then
  echo "=== Building pure OM-2 Zero-CUDA ufbi_check9_gb10 on Spark ==="
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
        '$REMOTE_DIR/src/ufbi_check9_gb10.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_check9_gb10'
    chmod 755 '$REMOTE_DIR/build/ufbi_check9_gb10'
    ls -la '$REMOTE_DIR/build/ufbi_check9_gb10'
    sha256sum '$REMOTE_DIR/build/ufbi_check9_gb10'
    file '$REMOTE_DIR/build/ufbi_check9_gb10'
  "
  echo "=== Running ufbi_check9_gb10 on live GB10 under spark-window + spark-receipt ==="
  ssh spark "set -eu
    echo \"\$(date -u +%FT%H:%MZ) CLAIM agy-yang ufbi-check9-gb10 to all: GB10 chip lock (lease 15m, --quiet none) for pure-OM-2 Zero-CUDA Check #9 (12-pt beta=0.10..10.0 calibration + 16^4 blocked-action tomography + k=3 32^4 RG flow)\" >> ~/handoffs/BOARD.md
    WID=\$(spark-window open ufbi-check9-gb10 --wait --lease 15 --gb10 exclusive --quiet none | tail -n 1)
    cleanup() {
      spark-window close \"\$WID\" >/dev/null 2>&1 || true
      echo \"\$(date -u +%FT%H:%MZ) RELEASE agy-yang ufbi-check9-gb10: done, GPU idle\" >> ~/handoffs/BOARD.md
    }
    trap cleanup EXIT
    spark-window run spark-receipt ufbi-check9-gb10 --idle 5 -- sh -c '$REMOTE_DIR/build/ufbi_check9_gb10 > $REMOTE_DIR/evidence/check9_gb10_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/check9_gb10_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "check10" ]; then
  echo "=== Building pure OM-2 Zero-CUDA ufbi_check10_gb10 on Spark ==="
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
        '$REMOTE_DIR/src/ufbi_check10_gb10.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_check10_gb10'
    chmod 755 '$REMOTE_DIR/build/ufbi_check10_gb10'
    ls -la '$REMOTE_DIR/build/ufbi_check10_gb10'
    sha256sum '$REMOTE_DIR/build/ufbi_check10_gb10'
    file '$REMOTE_DIR/build/ufbi_check10_gb10'
  "
  echo "=== Running ufbi_check10_gb10 on live GB10 under spark-window + spark-receipt ==="
  ssh spark "set -eu
    echo \"\$(date -u +%FT%H:%MZ) CLAIM agy-yang ufbi-check10-gb10 to all: GB10 chip lock (lease 15m, --quiet none) for pure-OM-2 Zero-CUDA Check #10 (exact S^3 Schwinger-Dyson 5-operator Hamiltonian tomography on 16^4 and 32^4)\" >> ~/handoffs/BOARD.md
    WID=\$(spark-window open ufbi-check10-gb10 --wait --lease 15 --gb10 exclusive --quiet none | tail -n 1)
    cleanup() {
      spark-window close \"\$WID\" >/dev/null 2>&1 || true
      echo \"\$(date -u +%FT%H:%MZ) RELEASE agy-yang ufbi-check10-gb10: done, GPU idle\" >> ~/handoffs/BOARD.md
    }
    trap cleanup EXIT
    spark-window run spark-receipt ufbi-check10-gb10 --idle 5 -- sh -c '$REMOTE_DIR/build/ufbi_check10_gb10 > $REMOTE_DIR/evidence/check10_gb10_run.tsv'
    rc=\$?
    cat '$REMOTE_DIR/evidence/check10_gb10_run.tsv'
    exit \$rc
  "
elif [ "$MODE" = "dyadic_grid" ]; then
  ssh spark "sh '$REMOTE_DIR/scripts/check_dyadic_grid.sh' '$REMOTE_DIR' '$OMEGA_DIR/seed/out/omc'"
elif [ "$MODE" = "interval_cert" ]; then
  echo "=== Building & running pure OM-2 Zero-MC Interval-Arithmetic Verifier on Spark CPU ==="
  ssh spark "set -eu
    cd '$OMEGA_DIR'
    OMC=seed/out/omc
    {
      printf 'om2\n'
      cat '$REMOTE_DIR/src/ufbi_math.om' '$REMOTE_DIR/src/ufbi_ivmath.om' '$REMOTE_DIR/src/ufbi_interval_rg_cert.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_interval_rg_cert'
    chmod 755 '$REMOTE_DIR/build/ufbi_interval_rg_cert'
    sha256sum '$REMOTE_DIR/build/ufbi_interval_rg_cert'
    '$REMOTE_DIR/build/ufbi_interval_rg_cert' > '$REMOTE_DIR/evidence/phase3a_interval_rg_cert.tsv'
    cat '$REMOTE_DIR/evidence/phase3a_interval_rg_cert.tsv'
  "
elif [ "$MODE" = "phase3b_cert" ]; then
  echo "=== Building & running pure OM-2 Zero-MC Phase III-B Dual-Cliff Verifier on Spark CPU ==="
  ssh spark "set -eu
    cd '$OMEGA_DIR'
    OMC=seed/out/omc
    {
      printf 'om2\n'
      cat '$REMOTE_DIR/src/ufbi_math.om' '$REMOTE_DIR/src/ufbi_ivmath.om' '$REMOTE_DIR/src/ufbi_w2_dyadic.om' '$REMOTE_DIR/src/ufbi_phase3b_cert.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_phase3b_cert'
    chmod 755 '$REMOTE_DIR/build/ufbi_phase3b_cert'
    file '$REMOTE_DIR/build/ufbi_phase3b_cert'
    ldd '$REMOTE_DIR/build/ufbi_phase3b_cert' 2>&1 || true
    sha256sum '$REMOTE_DIR/build/ufbi_phase3b_cert'
    '$REMOTE_DIR/build/ufbi_phase3b_cert' > '$REMOTE_DIR/evidence/phase3b_dual_cliff_cert.tsv'
    cat '$REMOTE_DIR/evidence/phase3b_dual_cliff_cert.tsv'
  "
elif [ "$MODE" = "phase4_cert" ]; then
  echo "=== Building & running pure OM-2 Zero-MC Phase IV Dual-Cliff Verifier on Spark CPU ==="
  ssh spark "set -eu
    cd '$OMEGA_DIR'
    OMC=seed/out/omc
    {
      printf 'om2\n'
      cat '$REMOTE_DIR/src/ufbi_math.om' '$REMOTE_DIR/src/ufbi_ivmath.om' '$REMOTE_DIR/src/ufbi_w2_dyadic.om' '$REMOTE_DIR/src/ufbi_phase4_cert.om'
    } | \"\$OMC\" > '$REMOTE_DIR/build/ufbi_phase4_cert'
    chmod 755 '$REMOTE_DIR/build/ufbi_phase4_cert'
    ls -la '$REMOTE_DIR/build/ufbi_phase4_cert'
    file '$REMOTE_DIR/build/ufbi_phase4_cert'
    ldd '$REMOTE_DIR/build/ufbi_phase4_cert' 2>&1 || true
    sha256sum '$REMOTE_DIR/build/ufbi_phase4_cert'
    '$REMOTE_DIR/build/ufbi_phase4_cert' > '$REMOTE_DIR/evidence/phase4_dual_cliff_cert.tsv'
    cat '$REMOTE_DIR/evidence/phase4_dual_cliff_cert.tsv'
  "
elif [ "$MODE" = "proofs" ]; then
  echo "=== Checking zero-dependency Lean 4 bridge proofs/UfbiMassGap.lean on Spark ==="
  ssh spark "set -eu
    ~/.elan/bin/lean --version
    ~/.elan/bin/lean '$REMOTE_DIR/proofs/UfbiMassGap.lean'
    echo 'LEAN_PROOF_CHECK status=PASS file=proofs/UfbiMassGap.lean'
  "
elif [ "$MODE" = "openai_bridge" ]; then
  echo "=== Checking the Mathlib bridges and periodic SU(2) Wilson specialization on Spark ==="
  scp "$ROOT/proofs/OpenAiYmBridge.lean" "$ROOT/proofs/DobrushinShlosman.lean" "$ROOT/proofs/WilsonPolymerBridge.lean" "$ROOT/proofs/PhaseFourBridge.lean" "$ROOT/proofs/OneLinkTransport.lean" "$ROOT/proofs/FundamentalSU2.lean" "$ROOT/proofs/PeriodicWilson.lean" "$ROOT/proofs/WilsonConditional.lean" "$ROOT/proofs/WilsonAngle.lean" "$ROOT/proofs/WilsonRadialTransport.lean" spark:~/workspace/yang-lean-bridge/
  ssh spark "set -eu
    export PATH=\"\$HOME/.elan/bin:\$PATH\"
    cd ~/workspace/yang-lean-bridge
    lean --version
    lake build OpenAiYmBridge DobrushinShlosman WilsonPolymerBridge PhaseFourBridge
    bridge_out=\$(mktemp -d)
    trap 'rm -rf \"\$bridge_out\"' EXIT
    lake env sh -ec '
      export LEAN_PATH=\"\$1:\$LEAN_PATH\"
      lean -o \"\$1/OneLinkTransport.olean\" OneLinkTransport.lean
      lean -o \"\$1/FundamentalSU2.olean\" FundamentalSU2.lean
      lean -o \"\$1/PeriodicWilson.olean\" PeriodicWilson.lean
      lean -o \"\$1/WilsonConditional.olean\" WilsonConditional.lean
      lean -o \"\$1/WilsonAngle.olean\" WilsonAngle.lean
      lean WilsonRadialTransport.lean
    ' sh \"\$bridge_out\"
    echo 'LEAN_PHASE4_BRIDGES status=PASS'
  "
else
  echo "usage: $0 check1 | obs_synth | obs_synth_w2 | obs_synth_w3 | check3 | check4 | check5 | check6 | check7 | check8 | check9 | check10 | dyadic_grid | interval_cert | phase3b_cert | phase4_cert | proofs | openai_bridge" >&2
  exit 2
fi
