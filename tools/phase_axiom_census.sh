#!/usr/bin/env bash
# Phase Axiom Census runner with CLI prefix argument
set -eo pipefail

if [ $# -gt 0 ]; then
  TARGET_PREFIX="$1"
elif [ -n "${MODULE_PREFIX}" ]; then
  TARGET_PREFIX="${MODULE_PREFIX}"
elif [ -n "${PHASE_MODULE}" ]; then
  TARGET_PREFIX="${PHASE_MODULE}"
else
  TARGET_PREFIX="GromovCompactness"
fi

echo "Running Phase Axiom Census with scope: ${TARGET_PREFIX}..."
MODULE_PREFIX="${TARGET_PREFIX}" lake env lean tests/PhaseAxiomCensus.lean
