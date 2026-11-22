#!/usr/bin/env bash
# Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
# Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
# see LICENSE.md for details.
# This project is licensed under non-commercial use. If you wish to use this software in a
# commercial product, service, or enterprise environment, please contact the developer to purchase
# a commercial license or negotiate royalty terms.
# Authors: Pablo Suárez-Serrato (November 2026)
# Rebuild the web blueprint and export its dependency graph as a static PDF for the report.
# Requires the conda env `leanblueprint` (graphviz + pygraphviz + leanblueprint).
set -euo pipefail
cd "$(dirname "$0")/.."
source ~/anaconda3/etc/profile.d/conda.sh
conda activate leanblueprint
leanblueprint web
python3 - <<'PY'
import re
s = open('blueprint/web/dep_graph_document.html').read()
dot = re.search(r'renderDot\(`(.*?)`\)', s, re.S).group(1)
dot = dot.replace('bgcolor=transparent', 'bgcolor=white, nodesep=0.08, ranksep=1.15, margin=0', 1).replace('penwidth=1.8', 'penwidth=1.8, fontsize=20, margin="0.04,0.02"', 1)
open('blueprint/dep_graph.dot', 'w').write(dot)
PY
dot -Tpdf blueprint/dep_graph.dot -o report/blueprint_dep_graph.pdf
echo "Wrote report/blueprint_dep_graph.pdf"
