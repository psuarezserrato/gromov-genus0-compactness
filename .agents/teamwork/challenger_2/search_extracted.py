#!/usr/bin/env python3
import re

with open('/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/challenger_2/extracted_pdf_text.txt', 'r', encoding='utf-8') as f:
    text = f.read()

keywords = ['Section 6', 'ghost', 'degree', 'component bound', 'floor', 'special', '|V|', 'G04', 'F06']
for kw in keywords:
    matches = [m.start() for m in re.finditer(re.escape(kw), text, re.IGNORECASE)]
    print(f"Keyword '{kw}': {len(matches)} occurrences")
    for pos in matches[:5]:
        snippet = text[max(0, pos-100):min(len(text), pos+200)].replace('\n', ' ')
        print(f"  [{pos}]: {snippet}\n")
