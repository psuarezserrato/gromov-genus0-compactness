#!/usr/bin/env python3
# Copyright (c) 2026 Pablo Suárez-Serrato. All rights reserved.
# Released under the GNU Affero General Public License v3.0 (AGPLv3) for non-commercial use;
# see LICENSE.md for details.
# This project is licensed under non-commercial use. If you wish to use this software in a
# commercial product, service, or enterprise environment, please contact the developer to purchase
# a commercial license or negotiate royalty terms.
# Authors: Pablo Suárez-Serrato (November 2026)
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
