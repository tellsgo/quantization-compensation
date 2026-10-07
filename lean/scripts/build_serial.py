#!/usr/bin/env python3
from pathlib import Path
import json, subprocess
root=Path(__file__).resolve().parents[1]
mods={x['module']:x for x in json.loads((root/'CLAIMS.json').read_text())['modules']};done=set()
while len(done)<len(mods):
    ready=[n for n,x in mods.items() if n not in done and all(i not in mods or i in done for i in x['imports'])]
    if not ready:raise SystemExit('Import cycle')
    for n in ready:
        subprocess.run(['lake','build',n],cwd=root,check=True);done.add(n)
subprocess.run(['lake','build'],cwd=root,check=True)
