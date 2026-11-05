import re

with open("blueprint/src/content.tex", "r") as f:
    text = f.read()

pattern = re.compile(r"\\begin\{(definition|theorem|lemma|proposition|corollary)\}(?:\[(.*?)\])?(.*?)\\end\{\1\}", re.DOTALL)

items = []
for m in pattern.finditer(text):
    env = m.group(1)
    name = m.group(2) or ""
    body = m.group(3)
    
    label_match = re.search(r"\\label\{([^}]+)\}", body)
    label = label_match.group(1) if label_match else None
    
    lean_match = re.search(r"\\lean\{([^}]+)\}", body)
    lean_path = lean_match.group(1) if lean_match else None
    
    has_leanok = "\\leanok" in body
    
    rest = text[m.end():m.end()+400]
    proof_match = re.match(r"\s*\\begin\{proof\}(.*?)\\end\{proof\}", rest, re.DOTALL)
    has_proof = bool(proof_match)
    proof_leanok = "\\leanok" in proof_match.group(1) if proof_match else False
    
    items.append({
        "env": env,
        "name": name,
        "label": label,
        "lean": lean_path,
        "has_leanok": has_leanok,
        "has_proof": has_proof,
        "proof_leanok": proof_leanok
    })

print("Total items parsed:", len(items))
print("Items with leanok:", sum(1 for x in items if x["has_leanok"]))
print("Items with proof:", sum(1 for x in items if x["has_proof"]))
print("Items with proof leanok:", sum(1 for x in items if x["proof_leanok"]))

print("\n--- Items with leanok ---")
for x in items:
    if x["has_leanok"]:
        lbl = x["label"] or "None"
        lp = x["lean"] or "None"
        print("%-32s | %s" % (lbl, lp))

print("\n--- Items WITHOUT leanok ---")
for x in items:
    if not x["has_leanok"]:
        lbl = x["label"] or "None"
        lp = x["lean"] or "None"
        print("%-32s | %s" % (lbl, lp))
