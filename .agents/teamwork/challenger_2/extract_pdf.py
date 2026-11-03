#!/usr/bin/env python3
import sys, os, zlib, re

def main():
    with open('/Users/pablosuarez/Desktop/SympTopAutoForm/gromov_compactness.pdf', 'rb') as f:
        data = f.read()

    streams = re.findall(b'stream[\r\n]+(.*?)[\r\n]+endstream', data, re.DOTALL)
    text = []
    for s in streams:
        try:
            decomp = zlib.decompress(s)
            words = re.findall(rb'\(([^\)]+)\)', decomp)
            if words:
                text.append(b' '.join(words).decode('latin1', errors='ignore'))
        except Exception:
            pass

    full_text = '\n'.join(text)
    
    with open('/Users/pablosuarez/Desktop/SympTopAutoForm/.agents/teamwork/challenger_2/extracted_pdf_text.txt', 'w', encoding='utf-8') as out:
        out.write(full_text)

    print(f"Wrote {len(full_text)} characters to extracted_pdf_text.txt")

if __name__ == '__main__':
    main()
