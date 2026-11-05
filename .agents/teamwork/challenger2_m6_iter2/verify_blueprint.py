import re
import sys

def verify():
    with open("blueprint/src/content.tex", "r") as f:
        content = f.read()

    lines = content.splitlines()
    failures = []

    # 1. Environment Matching
    env_stack = []
    env_regex = re.compile(r"\\(begin|end)\{([a-zA-Z0-9*]+)\}")
    for line_no, line in enumerate(lines, 1):
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

    # 3. Curly Braces Matching
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
                    failures.append(f"Line {line_no}: Negative brace depth")
                    brace_depth = 0
    if brace_depth != 0:
        failures.append(f"End of file: Non-zero brace depth ({brace_depth})")

    # 4. Dollar Sign Balancing per Paragraph
    paragraphs = content.split("\n\n")
    for p_idx, p in enumerate(paragraphs, 1):
        clean_p = "\n".join([re.sub(r"(?<!\\)%.*", "", l) for l in p.splitlines()])
        clean_p = clean_p.replace(r"\$", "").replace("$$", "")
        single_dollars = clean_p.count("$")
        if single_dollars % 2 != 0:
            failures.append(f"Paragraph {p_idx}: Unmatched inline math dollar signs (count={single_dollars})")

    # 5. PlasTeX Tagging Discipline
    phase3_labels = [
        "c01:weak_measures", "c02:concentration_data", "c03:defect_identity",
        "b03:neck_vanishing", "b04:one_level_decomp", "b05:ghost_branching",
        "b06:rank_decrease", "b07:local_tree",
        "g01:global_assembly", "g02:root_stabilization", "g03:master_compactness",
        "g04:component_bounds", "g05:final_gate",
        "e01:homology", "e02:automorphisms", "e03:marked",
        "e04:nodal_input", "e05:moduli_topology"
    ]

    a_labels = [
        "a01:mean_value", "a02:bochner", "a03:eps_regularity", "a04:elliptic_toolkit",
        "a05:bootstrap", "a06:local_compactness", "a07:sphere_energy_gap", "a08:monotonicity",
        "a09:cylinder_localization", "a10:cylinder_decay", "a11:puncture_extension",
        "a12:removal_of_singularities"
    ]

    item_pattern = re.compile(r"\\begin\{(definition|theorem|lemma|proposition|corollary)\}(?:\[(.*?)\])?(.*?)\\end\{\1\}", re.DOTALL)

    parsed_items = {}
    for m in item_pattern.finditer(content):
        env = m.group(1)
        body = m.group(3)
        l_match = re.search(r"\\label\{([^}]+)\}", body)
        if l_match:
            lbl = l_match.group(1)
            parsed_items[lbl] = (env, body, m.end())

    # Check Phase 3
    for lbl in phase3_labels:
        if lbl in parsed_items:
            env, body, end_pos = parsed_items[lbl]
            if "\\leanok" in body:
                failures.append(f"Phase 3 leak: {lbl} contains \\leanok in environment header")
            # check proof if any
            rest = content[end_pos:end_pos+400]
            pr_match = re.match(r"\s*\\begin\{proof\}(.*?)\\end\{proof\}", rest, re.DOTALL)
            if pr_match and "\\leanok" in pr_match.group(1):
                failures.append(f"Phase 3 leak: {lbl} contains \\leanok in proof block")

    # Check A01-A12
    for lbl in a_labels:
        if lbl not in parsed_items:
            failures.append(f"Missing contract {lbl}")
            continue
        env, body, end_pos = parsed_items[lbl]
        if "\\leanok" not in body:
            failures.append(f"A-contract {lbl} missing \\leanok in header")
        if not re.search(r"\\lean\{GromovCompactness\.Analysis\.[a-zA-Z0-9_]+\}", body):
            failures.append(f"A-contract {lbl} missing valid \\lean binding")
        rest = content[end_pos:end_pos+400]
        pr_match = re.match(r"\s*\\begin\{proof\}(.*?)\\end\{proof\}", rest, re.DOTALL)
        if not pr_match:
            failures.append(f"A-contract {lbl} missing proof block")
        elif "\\leanok" in pr_match.group(1):
            failures.append(f"A-contract {lbl} has premature \\leanok in proof block (should be omitted for Model A leaves)")

    # Check B01
    if "b01:threshold_h" in parsed_items:
        env, body, _ = parsed_items["b01:threshold_h"]
        if "\\leanok" not in body:
            failures.append("b01:threshold_h missing \\leanok")
        if "\\lean{GromovCompactness.Bubbling.TargetThresholds}" not in body:
            failures.append(f"b01:threshold_h has incorrect lean target: {body}")

    # Check B02
    if "b02:calibration" in parsed_items:
        env, body, end_pos = parsed_items["b02:calibration"]
        if "\\leanok" not in body:
            failures.append("b02:calibration missing \\leanok in header")
        if "\\lean{GromovCompactness.Bubbling.exists_calibrated_rescaling}" not in body:
            failures.append(f"b02:calibration does not point to GromovCompactness.Bubbling.exists_calibrated_rescaling: {body}")
        rest = content[end_pos:end_pos+400]
        pr_match = re.match(r"\s*\\begin\{proof\}(.*?)\\end\{proof\}", rest, re.DOTALL)
        if not pr_match:
            failures.append("b02:calibration missing proof block")
        elif "\\leanok" not in pr_match.group(1):
            failures.append("b02:calibration missing \\leanok in proof block (it is 0-sorry verified!)")

    print(f"Total verification failures: {len(failures)}")
    for f in failures:
        print("[-] ", f)
    if not failures:
        print("[+] ALL CHECKS PASSED PERFECTLY!")

if __name__ == "__main__":
    verify()
