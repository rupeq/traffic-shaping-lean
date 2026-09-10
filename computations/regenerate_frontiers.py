"""Optional: rerun all 79 LPs; outputs a new file, preserving stored witnesses."""
import json
from pathlib import Path
from fractions import Fraction
from covering import solve
from independent_certificate_check import check

root = Path(__file__).resolve().parent
saved = json.loads((root / 'FRONTIERS.json').read_text())['records']
fresh = []
for i, old in enumerate(saved, 1):
    new = solve(old['horizon'], old['delay'], old['max_arrivals'], old['total_cap'],
                causal=old['causal'], certify=True)
    check(new)
    assert Fraction(new['certificate']['delta']) == Fraction(old['certificate']['delta'])
    fresh.append(new)
    print(f"{i}/{len(saved)}: H={new['horizon']}, D={new['delay']}, B={new['total_cap']}, delta={new['certificate']['delta']}", flush=True)
(root / 'REGENERATED-FRONTIERS.json').write_text(json.dumps(dict(records=fresh), indent=2)+'\n')
