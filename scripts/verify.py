#!/usr/bin/env python3
"""Build the first batch and audit the listed transitive axiom dependencies."""
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
env = dict(os.environ)
evidence = root / 'verification'
evidence.mkdir(exist_ok=True)

def run(args, log):
    with (evidence / log).open('w') as stream:
        p = subprocess.run(args, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
    text = (evidence / log).read_text()
    print(text, end='')
    if p.returncode:
        raise SystemExit(p.returncode)
    return text

version = run(['lean', '--version'], 'toolchain.log').strip()
if 'version 4.34.1,' not in version:
    raise SystemExit('Unexpected Lean toolchain')
pins = {'fsfltz': '1a3d387cfacc746e25aad31e5b27b1803103e7cb',
        'mathlib': 'd13f23b723b8a846827a245b89c10fc7d3f11612'}
for package, revision in pins.items():
    actual = subprocess.check_output(['git', '-C', str(root/'.lake/packages'/package),
                                      'rev-parse', 'HEAD'], text=True).strip()
    if actual != revision:
        raise SystemExit(f'Unexpected revision for {package}: {actual}')
run(['lake', 'build'], 'build.log')
audit = run(['lake', 'env', 'lean', 'verification/AxiomAudit.lean'], 'axioms.log')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit, re.S)
no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", audit)
expected = re.findall(r'^#print axioms (\S+)', (evidence/'AxiomAudit.lean').read_text(), re.M)
reported = {name for name, _ in entries} | set(no_axioms)
if set(expected) != reported:
    raise SystemExit(f'Axiom audit declaration mismatch: {set(expected) ^ reported}')
for name, raw in entries:
    actual = {x.strip() for x in raw.split(',') if x.strip()}
    if actual - allowed:
        raise SystemExit(f'Unexpected axioms for {name}: {actual - allowed}')
sources = list(root.glob('ClusterSkeleton/**/*.lean')) + [root/'ClusterSkeleton.lean']
for source in sources:
    if re.search(r'^\s*(?:axiom|opaque)\b|\bsorry\b', source.read_text(), re.M):
        raise SystemExit(f'Forbidden proof placeholder in {source}')
result = {
    'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'build': 'passed', 'axiom_audit': 'passed',
    'lean_version': version, 'dependency_commits': pins,
    'allowed_axioms': sorted(allowed),
    'audited_declarations': expected,
    'first_geometric_target': 'defined; not proved',
    'source_sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
}
(evidence/'first-batch.json').write_text(json.dumps(result, indent=2)+'\n')
print('FIRST_BATCH_VERIFIED')
