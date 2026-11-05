#!/usr/bin/env python3
"""Write Maroti.lean so that it imports every file under Maroti/. With --check, only report."""
import pathlib, sys
root = pathlib.Path(__file__).resolve().parent.parent
mods = sorted('.'.join(p.relative_to(root).with_suffix('').parts) for p in (root / 'Maroti').rglob('*.lean'))
text = 'module\n\n' + ''.join(f'public import {m}\n' for m in mods)
out = root / 'Maroti.lean'
if '--check' in sys.argv:
    if out.read_text() != text:
        sys.exit('Maroti.lean does not import exactly the files under Maroti/; run tools/gen_root.py')
else:
    out.write_text(text)
