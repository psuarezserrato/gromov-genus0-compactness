import re
import sys
import io

sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8')

with open('GROMOV_COMPACTNESS_BLUEPRINT.md', 'r', encoding='utf-8') as f:
    text = f.read()

expected_contracts = [
    'F00', 'F01', 'F02', 'F03', 'F04', 'F05', 'F06',
    'A01', 'A02', 'A03', 'A04', 'A05', 'A06', 'A07', 'A08', 'A09', 'A10', 'A11', 'A12',
    'C01', 'C02', 'C03',
    'B01', 'B02', 'B03', 'B04', 'B05', 'B06', 'B07',
    'G01', 'G02', 'G03', 'G04', 'G05',
    'E01', 'E02', 'E03', 'E04', 'E05'
]

print(f"Total expected contracts: {len(expected_contracts)}")

contract_details = []

for c in expected_contracts:
    pattern = rf'#### Task {c}:[^\n]+'
    m = re.search(pattern, text)
    if not m:
        print(f"ERROR: Contract {c} not found!")
        continue
    pos = m.start()
    # Find next task header or end of section
    next_m = re.search(r'\n#### Task [A-Z0-9]+:', text[pos+10:])
    if not next_m:
        next_m = re.search(r'\n## [0-9]', text[pos+10:])
    end_pos = pos + 10 + next_m.start() if next_m else pos + 4000
    chunk = text[pos:end_pos]
    
    title = m.group(0).strip()
    status_m = re.search(r'\*\*Status\*\*:\s*`?\[?([A-Z_]+)\]?`?', chunk)
    status = status_m.group(1) if status_m else 'UNKNOWN'
    
    file_m = re.search(r'\*\*Proposed File\*\*:\s*`([^`]+)`', chunk)
    prop_file = file_m.group(1) if file_m else 'UNKNOWN'
    
    deps_m = re.search(r'\*\*Dependencies\*\*:\s*([^\n]+)', chunk)
    deps = deps_m.group(1).strip() if deps_m else 'UNKNOWN'
    
    has_spec = '**Mathematical Specification**:' in chunk
    has_lean = '```lean' in chunk
    has_docstring = ('/--' in chunk) or ('/-!' in chunk) or has_spec
    
    contract_details.append({
        'id': c,
        'title': title,
        'status': status,
        'file': prop_file,
        'deps': deps,
        'has_spec': has_spec,
        'has_lean': has_lean,
        'has_docstring': has_docstring,
    })

print(f"Successfully parsed {len(contract_details)} contracts.")

status_counts = {}
for cd in contract_details:
    st = cd['status']
    status_counts[st] = status_counts.get(st, 0) + 1
    if not cd['has_lean']:
        print(f"CRITICAL: Contract {cd['id']} missing Lean code!")
    if not cd['has_spec']:
        print(f"CRITICAL: Contract {cd['id']} missing Mathematical Specification!")

print("\nStatus counts across 39 contracts:")
for st, cnt in sorted(status_counts.items()):
    print(f"  {st}: {cnt}")

print(f'{"ID":<5} | {"Status":<22} | {"Proposed File":<48} | {"Dependencies"}')
print('-'*110)
for cd in contract_details:
    print(f"{cd['id']:<5} | {cd['status']:<22} | {cd['file']:<48} | {cd['deps']}")
