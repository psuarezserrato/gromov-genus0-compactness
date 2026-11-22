#!/usr/bin/env bash
# Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
# Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
# see LICENSE.md for details.
# This project is licensed under non-commercial use. If you wish to use this software in a
# commercial product, service, or enterprise environment, please contact the developer to purchase
# a commercial license or negotiate royalty terms.
# Authors: Pablo Suárez-Serrato (November 2026)
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
