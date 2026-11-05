import re
import sys

def run_adversarial_checks():
    failures = []
    
    with open("blueprint/src/content.tex", "r") as f:
        content = f.read()

    lines = content.splitlines()
    
    # 1. Environment Matching
    env_stack = []
    env_regex = re.compile(r"\\(begin|end)\{([a-zA-Z0-9*]+)\}")
    for line_no, line in enumerate(lines, 1):
        # strip comments
        clean_line = re.sub(r"(?<!\\)%.*", "", line)
        for m in env_regex.finditer(clean_line):
            tag_type, env_name = m.group(1), m.group(2)
            if tag_type == "begin":
                env_stack.append((env_name, line_no))
            elif tag_type == "end":
                if not env_stack:
                    failures.append(f"Line {line_no}: Unexpected \\end{{{env_name}}} with empty stack")
                else:
                    last_env, start_line = env_stack.pop()
                    if last_env != env_name:
                        failures.append(f"Line {line_no}: Mismatched \\end{{{env_name}}}, expected \\end{{{last_env}}} opened at line {start_line}")
                        
    if env_stack:
        for env_name, line_no in env_stack:
            failures.append(f"Line {line_no}: Unclosed \\begin{{{env_name}}}")

    # 2. Display Math Matching \[ and \]
    open_brackets = 0
    for line_no, line in enumerate(lines, 1):
        clean_line = re.sub(r"(?<!\\)%.*", "", line)
        opens = len(re.findall(r"\\\[", clean_line))
        closes = len(re.findall(r"\\\]", clean_line))
        open_brackets += opens - closes
        if open_brackets < 0:
            failures.append(f"Line {line_no}: Stray \\] without matching \\[")
            open_brackets = 0
    if open_brackets > 0:
        failures.append(f"End of file: {open_brackets} unclosed \\[ display math environments")

    # 3. Curly Braces Matching (ignoring \{, \}, and comments)
    brace_depth = 0
    for line_no, line in enumerate(lines, 1):
        clean_line = re.sub(r"(?<!\\)%.*", "", line)
        clean_line = clean_line.replace(r"\{", "").replace(r"\}", "")
        for char in clean_line:
            if char == "{":
                brace_depth += 1
            elif char == "}":
                brace_depth -= 1
                if brace_depth < 0:
                    failures.append(f"Line {line_no}: Negative brace depth (stray closing brace)")
                    brace_depth = 0
    if brace_depth != 0:
        failures.append(f"End of file: Non-zero brace depth ({brace_depth})")

    # 4. Dollar Sign Balancing per Paragraph (blank lines separate paragraphs)
    paragraphs = content.split("\n\n")
    for p_idx, p in enumerate(paragraphs, 1):
        clean_p = "\n".join([re.sub(r"(?<!\\)%.*", "", l) for l in p.splitlines()])
        # Count unescaped single dollars
        # replace escaped \$
        clean_p = clean_p.replace(r"\$", "")
        # replace double dollars $$
        clean_p = clean_p.replace("$$", "")
        single_dollars = clean_p.count("$")
        if single_dollars % 2 != 0:
            failures.append(f"Paragraph {p_idx}: Unmatched inline math dollar signs (count={single_dollars}):\n{p[:150]}...")

    # 5. PlasTeX Tagging Discipline
    # Phase 3 items: c01-c03, b03-b07, g01-g05, e01-e05
    phase3_labels = [
        "c01:weak_measures", "c02:concentration_data", "c03:defect_identity",
        "b03:neck_vanishing", "b04:one_level_decomp", "b05:ghost_branching",
        "b06:rank_decrease", "b07:local_tree",
        "g01:global_assembly", "g02:root_stabilization", "g03:master_compactness",
        "g04:component_bounds", "g05:final_gate",
        "e01:homology", "e02:automorphisms", "e03:marked",
        "e04:nodal_input", "e05:moduli_topology"
    ]
    
    # Phase 2 items: a01-a12, b01-b02
    phase2_labels = [
        "a01:mean_value", "a02:bochner", "a03:eps_regularity", "a04:elliptic_toolkit",
        "a05:bootstrap", "a06:local_compactness", "a07:sphere_energy_gap", "a08:monotonicity",
        "a09:cylinder_localization", "a10:cylinder_decay", "a11:puncture_extension",
        "a12:removal_of_singularities", "b01:threshold_h", "b02:calibration"
    ]

    item_pattern = re.compile(r"\\begin\{(definition|theorem|lemma|proposition|corollary)\}(?:\[(.*?)\])?(.*?)\\end\{\1\}", re.DOTALL)
    
    parsed_labels = set()
    for m in item_pattern.finditer(content):
        env = m.group(1)
        body = m.group(3)
        l_match = re.search(r"\\label\{([^}]+)\}", body)
        if not l_match:
            failures.append(f"Item near position {m.start()}: Missing \\label")
            continue
        lbl = l_match.group(1)
        parsed_labels.add(lbl)
        
        has_leanok = "\\leanok" in body
        
        # Check Phase 3 discipline
        if lbl in phase3_labels and has_leanok:
            failures.append(f"VIOLATION: Phase 3 item {lbl} has premature \\leanok tag!")
            
        # Check Phase 2 discipline
        if lbl in phase2_labels:
            if not has_leanok:
                failures.append(f"VIOLATION: Phase 2 item {lbl} is missing \\leanok tag!")
            # If theorem/lemma, must have proof with leanok
            if env in ["theorem", "lemma", "proposition", "corollary"]:
                rest = content[m.end():m.end()+400]
                pr_match = re.match(r"\s*\\begin\{proof\}(.*?)\\end\{proof\}", rest, re.DOTALL)
                if not pr_match:
                    failures.append(f"VIOLATION: Phase 2 theorem {lbl} is missing \\begin{{proof}} block!")
                elif "\\leanok" not in pr_match.group(1):
                    failures.append(f"VIOLATION: Phase 2 proof for {lbl} is missing \\leanok!")

    # Verify all expected phase 2 and phase 3 labels were parsed
    for l in phase2_labels:
        if l not in parsed_labels:
            failures.append(f"Missing Phase 2 label in content.tex: {l}")
    for l in phase3_labels:
        if l not in parsed_labels:
            failures.append(f"Missing Phase 3 label in content.tex: {l}")

    print(f"Adversarial checks completed with {len(failures)} failures.")
    for f in failures:
        print("[-] FAILURE:", f)
    if not failures:
        print("[+] ALL ADVERSARIAL CHECKS PASSED PERFECTLY!")

if __name__ == "__main__":
    run_adversarial_checks()
