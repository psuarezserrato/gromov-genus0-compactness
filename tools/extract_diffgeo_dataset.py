#!/usr/bin/env python3
"""
extract_diffgeo_dataset.py — Extract Sorry-Free (goal, proof) Pairs & Declarations
from Bennett Chow et al.'s differential-geometry (Lean v4.35.0) repository,
merge with GromovCompactness v4.35.0 proofs into stratified LoRA splits,
and merge DifferentialGeometry declarations into data/mathlib_project_declarations.jsonl.
"""

import os
import sys
import re
import json
import random
import bisect
from multiprocessing import Pool, cpu_count
from typing import Dict, List, Tuple, Any

SYSTEM_PROMPT = (
    "You are an expert Lean 4 (v4.35.0) formal mathematician and proof engineer "
    "specializing in symplectic topology, pseudo-holomorphic curves, differential geometry, "
    "elliptic PDEs, and Mathlib v4.35.0."
)

# High-value domain path keywords aligned with GromovCompactness & differential geometry
HIGH_VALUE_PATH_KEYWORDS = (
    "Analysis/Elliptic",
    "Analysis/Schauder",
    "Analysis/Sobolev",
    "Analysis/Complex",
    "Analysis/Calculus",
    "Analysis/Heat",
    "Analysis/Parabolic",
    "Analysis/Estimates",
    "Analysis/HoleFilling",
    "Analysis/Normed",
    "Analysis/Integration",
    "Geometry/MinimalSurface",
    "Geometry/HarmonicMap",
    "Geometry/Neck",
    "Geometry/Compactness",
    "Geometry/Conformal",
    "Geometry/Curvature",
    "Geometry/Metric",
    "Geometry/Measure",
    "Geometry/Submanifold",
    "Geometry/Operator",
    "Geometry/Geodesic",
    "Geometry/Gradient",
    "Geometry/VectorField",
    "Bundle/",
    "Tensor/",
    "Topology/Manifold",
    "Topology/Compactness",
    "Topology/MetricSpace",
    "Topology/EMetricSpace",
    "Topology/UniformConvergence",
    "Topology/Sphere",
    "Topology/Surface",
    "External/DeGiorgi",
    "External/RiemannMapping",
    "External/TauCeti",
)


def mask_comments_and_strings_fast(content: str) -> str:
    """
    Fast character-offset-preserving masker for Lean 4 line comments (--),
    block comments (/- ... -/), and string literals ("...").
    """
    result = list(content)
    n = len(content)
    i = 0
    while i < n:
        ch = content[i]
        if ch == '"':
            start = i
            i += 1
            while i < n and content[i] != '"':
                if content[i] == '\\' and i + 1 < n:
                    i += 2
                else:
                    i += 1
            if i < n:
                i += 1
            for k in range(start, i):
                if result[k] != '\n':
                    result[k] = ' '
        elif ch == '-' and i + 1 < n and content[i + 1] == '-':
            j = content.find('\n', i + 2)
            if j == -1:
                j = n
            for k in range(i, j):
                result[k] = ' '
            i = j
        elif ch == '/' and i + 1 < n and content[i + 1] == '-':
            depth = 1
            start = i
            i += 2
            while i < n and depth > 0:
                if content[i] == '/' and i + 1 < n and content[i + 1] == '-':
                    depth += 1
                    i += 2
                elif content[i] == '-' and i + 1 < n and content[i + 1] == '/':
                    depth -= 1
                    i += 2
                else:
                    i += 1
            for k in range(start, i):
                if result[k] != '\n':
                    result[k] = ' '
        else:
            i += 1
    return ''.join(result)


def find_declaration_assignment(masked_chunk: str, max_sig_scan: int = 3500) -> int:
    """
    Finds the index of the top-level declaration assignment := at bracket-depth 0.
    """
    p_depth = b_depth = c_depth = a_depth = 0
    n = min(len(masked_chunk), max_sig_scan)
    i = 0
    while i < n:
        ch = masked_chunk[i]
        if ch == '(':
            p_depth += 1
        elif ch == ')':
            p_depth = max(0, p_depth - 1)
        elif ch == '[':
            b_depth += 1
        elif ch == ']':
            b_depth = max(0, b_depth - 1)
        elif ch == '{':
            c_depth += 1
        elif ch == '}':
            c_depth = max(0, c_depth - 1)
        elif ch in ('⟨', '⦃'):
            a_depth += 1
        elif ch in ('⟩', '⦄'):
            a_depth = max(0, a_depth - 1)
        elif (p_depth + b_depth + c_depth + a_depth) == 0:
            if ch == ':' and i + 1 < len(masked_chunk) and masked_chunk[i + 1] == '=':
                return i
        i += 1
    return -1


def strip_trailing_block_comment(s: str) -> str:
    s = s.rstrip()
    if not s.endswith("-/"):
        return s
    depth = 0
    i = len(s)
    while i >= 2:
        if s[i - 2:i] == "-/":
            depth += 1
            i -= 2
        elif s[i - 2:i] == "/-":
            depth -= 1
            i -= 2
            if depth == 0:
                return s[:i].rstrip()
        else:
            i -= 1
    return s


def clean_proof_trailing(proof: str) -> str:
    while True:
        prev = proof
        proof = proof.rstrip()
        proof = re.sub(r'((?:^|\n)[ \t]*--[^\n]*)+$', '', proof).rstrip()
        proof = re.sub(r'((?:^|\n)[ \t]*[-=]{5,}[ \t]*)+$', '', proof).rstrip()
        proof = re.sub(r'((?:^|\n)[ \t]*#\w+[^\n]*)+$', '', proof).rstrip()
        stripped_bc = strip_trailing_block_comment(proof)
        if stripped_bc != proof:
            proof = stripped_bc.rstrip()
        if proof == prev:
            break
    return proof.strip()


LEAKED_CMD_PAT = re.compile(
    r'^[ \t]*(?:set_option|attribute|theorem|lemma|def|abbrev|structure|class|instance|open|namespace|section|end|variable|axiom)\b',
    re.MULTILINE
)

DECL_START_PAT = re.compile(
    r"^[ \t]*(?:(?:private|protected|noncomputable|scoped|local)\s+)*(theorem|lemma|def|abbrev)\s+([a-zA-Z0-9_\'\.]+)",
    re.MULTILINE
)

CMD_BOUNDARY_PAT = re.compile(
    r"^[ \t]*(?:/--[\s\S]*?-\/\s*)*(?:@\[[^\]]+\]\s*)*(?:(?:private|protected|noncomputable|scoped|local|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|coinductive|instance|example|axiom|opaque|mutual|"
    r"set_option|attribute|register_simp_attr|register_builtin_option|register_option|"
    r"open|namespace|section|end|variable|variables|universe|universes|export|import|"
    r"macro|macro_rules|syntax|elab|elab_rules|notation|infix|infixl|infixr|prefix|postfix|simproc|builtin_simproc|"
    r"initialize|builtin_initialize|deriving|"
    r"#\w+)\b",
    re.MULTILINE
)

SORRY_PAT = re.compile(r'\b(?:sorry(?:Ax)?|admit|axiom)\b')


def is_substantive_proof(proof: str, masked_proof: str) -> bool:
    if not proof or not proof.strip():
        return False
    if proof.count("/-") != proof.count("-/"):
        return False
    code_only = masked_proof.strip()
    if not code_only or code_only in ('by', 'rfl'):
        return code_only == 'rfl'
    if re.match(r'^by\b', code_only):
        tactic_part = re.sub(r'^by\b', '', code_only).strip()
        if not tactic_part:
            return False
    if proof.startswith((")", "]", "}", ":", "|")):
        return False
    if LEAKED_CMD_PAT.search(code_only):
        return False
    return True


def parse_single_lean_file(args: Tuple[str, str]) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    """
    Parses a single .lean file and returns:
      (proof_records, decl_records)
    """
    fpath, repo_root = args
    proof_records: List[Dict[str, Any]] = []
    decl_records: List[Dict[str, Any]] = []

    try:
        with open(fpath, "r", encoding="utf-8", errors="ignore") as f:
            content = f.read()
    except Exception:
        return proof_records, decl_records

    if not content:
        return proof_records, decl_records

    rel_file = os.path.relpath(fpath, repo_root)
    mod_name = rel_file[:-5].replace(os.sep, ".")

    masked = mask_comments_and_strings_fast(content)

    # Detect primary namespace if declared, else module name
    ns_match = re.search(r"^[ \t]*namespace\s+([a-zA-Z0-9_\.]+)", masked, re.MULTILINE)
    default_ns = ns_match.group(1) if ns_match else mod_name

    cmd_boundaries = [m.start() for m in CMD_BOUNDARY_PAT.finditer(content)]
    mod_doc_boundaries = [m.start() for m in re.finditer(r"^[ \t]*/-!", content, re.MULTILINE)]
    boundaries = sorted(set(cmd_boundaries + mod_doc_boundaries))
    boundaries.append(len(content))

    for m in DECL_START_PAT.finditer(masked):
        full_match_header = content[m.start():m.end()]
        if re.search(r"\bprivate\b", full_match_header):
            continue

        kind = m.group(1)
        raw_name = m.group(2)
        start = m.start()

        b_idx = bisect.bisect_right(boundaries, start)
        next_b = boundaries[b_idx] if b_idx < len(boundaries) else len(content)

        chunk = content[start:next_b]
        chunk_m = masked[start:next_b]

        # Skip any declaration referencing sorry, admit, or axiom
        if SORRY_PAT.search(chunk_m):
            continue

        idx = find_declaration_assignment(chunk_m)
        if idx == -1:
            continue

        raw_sig = chunk[:idx].strip()
        sig_m = chunk_m[:idx]

        # Balanced brackets in signature
        if (sig_m.count("(") != sig_m.count(")") or
            sig_m.count("[") != sig_m.count("]") or
            sig_m.count("{") != sig_m.count("}")):
            continue

        # Extract docstring immediately preceding declaration if present
        prefix = content[:start].rstrip()
        doc = ""
        if prefix.endswith("-/"):
            doc_start = prefix.rfind("/--")
            if doc_start != -1 and doc_start > prefix.rfind("/-!"):
                doc = prefix[doc_start + 3:-2].strip()
                if SORRY_PAT.search(doc):
                    doc = ""

        if "." in raw_name:
            full_name = raw_name if raw_name.startswith("DifferentialGeometry.") else f"{default_ns}.{raw_name}"
            short_name = raw_name.rsplit(".", 1)[-1]
        else:
            full_name = f"{default_ns}.{raw_name}"
            short_name = raw_name

        # Clean compact type signature for BM25 index
        compact_type = re.sub(
            r"^(?:(?:private|protected|noncomputable|scoped|local)\s+)*(?:theorem|lemma|def|abbrev)\s+[a-zA-Z0-9_\'\.]+\s*",
            "",
            raw_sig,
        ).strip()
        compact_type = re.sub(r"\s+", " ", compact_type)

        if len(compact_type) <= 1200:
            decl_kind = "thm" if kind in ("theorem", "lemma") else "def"
            decl_records.append({
                "doc": doc[:300] if doc else "",
                "kind": decl_kind,
                "module": mod_name,
                "name": full_name,
                "type": compact_type,
                "_file": rel_file,
            })

        # For proof dataset, only keep theorem/lemma
        if kind not in ("theorem", "lemma"):
            continue

        raw_proof = chunk[idx + 2:]
        clean_proof = clean_proof_trailing(raw_proof)
        if not clean_proof or len(clean_proof) > 3200 or len(raw_sig) > 2200:
            continue
        if len(raw_sig) + len(clean_proof) > 3800:
            continue

        if SORRY_PAT.search(clean_proof):
            continue

        p_masked = mask_comments_and_strings_fast(clean_proof)
        if not is_substantive_proof(clean_proof, p_masked):
            continue

        if (p_masked.count("(") != p_masked.count(")") or
            p_masked.count("[") != p_masked.count("]") or
            p_masked.count("{") != p_masked.count("}")):
            continue

        prompt_header = f"/-- {doc} -/\n" if doc else ""
        prompt_body = f"{prompt_header}{raw_sig}"

        user_content = f"Prove the following theorem:\n\n```lean4\n{prompt_body}\n```"
        assistant_content = f"```lean4\n{clean_proof}\n```"

        turn_user = (
            f"<start_of_turn>user\n"
            f"{SYSTEM_PROMPT}\n"
            f"{user_content}<end_of_turn>\n"
        )
        turn_model = f"<start_of_turn>model\n{assistant_content}<end_of_turn>\n"

        proof_records.append({
            "id": full_name,
            "name": short_name,
            "namespace": default_ns,
            "module": mod_name,
            "file": rel_file,
            "docstring": doc,
            "signature": raw_sig,
            "goal_type": raw_sig,
            "proof": clean_proof,
            "axioms": ["Classical.choice", "Quot.sound", "propext"],
            "premises_used": [],
            "turn_user": turn_user,
            "turn_model": turn_model,
        })

    return proof_records, decl_records


def score_diffgeo_record(rec: Dict[str, Any]) -> Tuple[int, int]:
    """
    Prioritizes high-value PDE / differential geometry / manifold / Sobolev / complex analysis
    theorems with substantive multi-step tactic proofs of moderate length (80..2200 chars).
    """
    fpath = rec.get("file", "")
    proof = rec.get("proof", "")
    plen = len(proof)

    priority = 0
    for idx, kw in enumerate(HIGH_VALUE_PATH_KEYWORDS):
        if kw in fpath:
            priority += 100 - idx
            break

    if 80 <= plen <= 1800:
        priority += 30
    elif 40 <= plen < 80:
        priority += 15
    if rec.get("docstring"):
        priority += 10

    return (priority, -abs(plen - 450))


def score_decl_record(d: Dict[str, Any]) -> Tuple[int, int]:
    fpath = d.get("_file", "")
    priority = 0
    for idx, kw in enumerate(HIGH_VALUE_PATH_KEYWORDS):
        if kw in fpath:
            priority += 100 - idx
            break
    if d.get("doc"):
        priority += 20
    return (priority, -len(d.get("type", "")))


def to_chat_split_item(rec: Dict[str, Any]) -> Dict[str, Any]:
    """
    Formats a record into the chat-formatted split schema with {"messages": [system, user, assistant]}.
    """
    doc = rec.get("docstring", "")
    sig = rec.get("signature", "")
    proof = rec.get("proof", "")
    prompt_header = f"/-- {doc} -/\n" if doc else ""
    prompt_body = f"{prompt_header}{sig}" if sig and not sig.startswith("/--") else (sig or prompt_header)

    user_msg = f"Prove the following theorem:\n\n```lean4\n{prompt_body}\n```"
    asst_msg = f"```lean4\n{proof}\n```"

    return {
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": user_msg},
            {"role": "assistant", "content": asst_msg},
        ]
    }


def main():
    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    diffgeo_root = "/tmp/differential-geometry"
    diffgeo_src = os.path.join(diffgeo_root, "DifferentialGeometry")

    if not os.path.isdir(diffgeo_src):
        print(f"[ERROR] {diffgeo_src} not found.", file=sys.stderr)
        sys.exit(1)

    lean_files: List[Tuple[str, str]] = []
    for root, _, files in os.walk(diffgeo_src):
        for fn in sorted(files):
            if fn.endswith(".lean"):
                lean_files.append((os.path.join(root, fn), diffgeo_root))

    print(f"Found {len(lean_files)} .lean files under {diffgeo_src}.")

    workers = min(cpu_count() or 4, 8)
    all_proofs: List[Dict[str, Any]] = []
    all_decls: List[Dict[str, Any]] = []

    with Pool(workers) as pool:
        for proof_recs, decl_recs in pool.imap_unordered(parse_single_lean_file, lean_files, chunksize=64):
            all_proofs.extend(proof_recs)
            all_decls.extend(decl_recs)

    # Deduplicate by id / name
    seen_proof_ids = set()
    unique_proofs = []
    for r in all_proofs:
        if r["id"] not in seen_proof_ids:
            seen_proof_ids.add(r["id"])
            unique_proofs.append(r)

    print(f"Extracted {len(unique_proofs)} unique sorry-free theorem/lemma proofs from differential-geometry.")
    print(f"Extracted {len(all_decls)} sorry-free declarations from differential-geometry.")

    # Sort by domain relevance and proof quality
    unique_proofs.sort(key=lambda r: (score_diffgeo_record(r), r["id"]), reverse=True)

    # Select top 3,330 high-value DifferentialGeometry proofs to pair with 2,670 GromovCompactness proofs (= 6,000 total)
    curated_diffgeo_count = min(3330, len(unique_proofs))
    curated_diffgeo = unique_proofs[:curated_diffgeo_count]

    diffgeo_jsonl = os.path.join(repo_root, "data", "diffgeo_accepted_proofs.jsonl")
    with open(diffgeo_jsonl, "w", encoding="utf-8") as f:
        for r in curated_diffgeo:
            f.write(json.dumps(r) + "\n")
    print(
        f"Saved {len(curated_diffgeo)} curated high-value differential-geometry proofs "
        f"(from {len(unique_proofs)} total sorry-free proofs) to {diffgeo_jsonl}."
    )

    # Load GromovCompactness 2,670 accepted proofs
    gromov_jsonl = os.path.join(repo_root, "data", "gemma_accepted_proofs.jsonl")
    gromov_proofs = []
    with open(gromov_jsonl, "r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                gromov_proofs.append(json.loads(line))
    print(f"Loaded {len(gromov_proofs)} GromovCompactness accepted proofs.")

    # Stratified 90% / 5% / 5% split across both repositories
    rng = random.Random(42)
    gromov_shuf = list(gromov_proofs)
    diffgeo_shuf = list(curated_diffgeo)
    rng.shuffle(gromov_shuf)
    rng.shuffle(diffgeo_shuf)

    def split_90_5_5(items: List[Dict[str, Any]]):
        n = len(items)
        n_val = int(round(n * 0.05))
        n_test = int(round(n * 0.05))
        n_train = n - n_val - n_test
        return items[:n_train], items[n_train:n_train + n_val], items[n_train + n_val:]

    g_train, g_val, g_test = split_90_5_5(gromov_shuf)
    d_train, d_val, d_test = split_90_5_5(diffgeo_shuf)

    train_items = [to_chat_split_item(r) for r in (g_train + d_train)]
    val_items = [to_chat_split_item(r) for r in (g_val + d_val)]
    test_items = [to_chat_split_item(r) for r in (g_test + d_test)]

    rng.shuffle(train_items)
    rng.shuffle(val_items)
    rng.shuffle(test_items)

    splits_dir = os.path.join(repo_root, "data", "lora_splits")
    os.makedirs(splits_dir, exist_ok=True)

    for split_name, split_data in [("train", train_items), ("valid", val_items), ("test", test_items)]:
        out_path = os.path.join(splits_dir, f"{split_name}.jsonl")
        with open(out_path, "w", encoding="utf-8") as f:
            for item in split_data:
                f.write(json.dumps(item) + "\n")
        print(f"Wrote {len(split_data)} records to {out_path}.")

    # Merge deduplicated high-value DifferentialGeometry declarations into data/mathlib_project_declarations.jsonl
    # Cap added declarations to top 10,000 high-value declarations so bm25_index.pkl stays < 100 MB (GitHub limit) and < 3.5ms latency
    decl_jsonl = os.path.join(repo_root, "data", "mathlib_project_declarations.jsonl")
    existing_decls: List[Dict[str, Any]] = []
    seen_decl_names = set()
    if os.path.isfile(decl_jsonl):
        with open(decl_jsonl, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    d = json.loads(line)
                    name = d.get("name", "")
                    mod = d.get("module", "")
                    if name and not mod.startswith("DifferentialGeometry.") and name not in seen_decl_names:
                        seen_decl_names.add(name)
                        existing_decls.append(d)
                except Exception:
                    pass

    all_decls.sort(key=lambda d: (score_decl_record(d), d.get("name", "")), reverse=True)
    added_decls = 0
    max_diffgeo_decls = 5000
    for d in all_decls:
        if added_decls >= max_diffgeo_decls:
            break
        name = d.get("name", "")
        if name and name not in seen_decl_names:
            seen_decl_names.add(name)
            d_clean = {
                "doc": d["doc"],
                "kind": d["kind"],
                "module": d["module"],
                "name": d["name"],
                "type": d["type"],
            }
            existing_decls.append(d_clean)
            added_decls += 1

    with open(decl_jsonl, "w", encoding="utf-8") as f:
        for d in existing_decls:
            f.write(json.dumps(d) + "\n")

    print(
        f"Updated {decl_jsonl}: added {added_decls} curated DifferentialGeometry declarations "
        f"(from {len(all_decls)} total extracted; combined index declarations: {len(existing_decls)})."
    )


if __name__ == "__main__":
    main()
