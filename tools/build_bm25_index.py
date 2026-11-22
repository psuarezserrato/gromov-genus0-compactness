#!/usr/bin/env python3
# Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
# Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
# see LICENSE.md for details.
# This project is licensed under non-commercial use. If you wish to use this software in a
# commercial product, service, or enterprise environment, please contact the developer to purchase
# a commercial license or negotiate royalty terms.
# Authors: Pablo Suárez-Serrato (November 2026)
"""
build_bm25_index.py — Rebuild data/bm25_index.pkl from data/mathlib_project_declarations.jsonl
and benchmark sub-5ms retrieval latency.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from premise_retrieval import PremiseRetriever, run_benchmark


def main():
    retriever = PremiseRetriever.build()
    run_benchmark(retriever)


if __name__ == "__main__":
    main()
