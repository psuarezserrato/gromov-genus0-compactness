#!/usr/bin/env python3
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
