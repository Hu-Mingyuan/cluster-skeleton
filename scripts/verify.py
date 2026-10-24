#!/usr/bin/env python3
"""Build the complete library and audit the final theorem and project declarations.

Run after scripts/fetch-cache.sh. Dependency revisions and clean worktrees are
checked before and after building. All compilation and audit inputs must retain
the same hashes throughout verification.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'verification'
ENV = dict(os.environ)
ENV.setdefault('MATHLIB_NO_CACHE_ON_UPDATE', '1')
ENV.setdefault('LEAN_NUM_THREADS', '2')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FINAL_TARGET = 'ClusterSkeleton.FullSkeleton.firstGeometricTarget'


def source_snapshot():
    sources = sorted((ROOT / 'ClusterSkeleton').rglob('*.lean'))
    inputs = sources + [ROOT / name for name in (
        'ClusterSkeleton.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
        'verification/FullSkeletonConsumer.lean', 'verification/AxiomAudit.lean',
        'verification/accepted-library.json', 'scripts/verify.py')]
    return {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in inputs}


def dependency_revisions():
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    pins = {}
    for package in manifest['packages']:
        if package['type'] != 'git':
            raise RuntimeError(f'Unexpected dependency type: {package["name"]}')
        name, expected = package['name'], package['rev']
        command = ['git', '-C', str(ROOT / '.lake/packages' / name)]
        actual = subprocess.check_output(command + ['rev-parse', 'HEAD'],
                                         text=True, env=ENV).strip()
        if actual != expected:
            raise RuntimeError(f'Unexpected revision for {name}: {actual}; expected {expected}')
        if subprocess.check_output(command + ['status', '--porcelain', '--untracked-files=all'],
                                   env=ENV):
            raise RuntimeError(f'Modified dependency worktree: {name}')
        pins[name] = actual
    return pins


def run(args, log):
    started = time.monotonic()
    print('Checking:', ' '.join(args), flush=True)
    path = EVIDENCE / log
    with path.open('w', encoding='utf-8') as stream:
        proc = subprocess.run(args, cwd=ROOT, env=ENV, stdout=stream, stderr=subprocess.STDOUT)
    output = path.read_text(encoding='utf-8')
    if proc.returncode:
        print(output[-16000:], end='')
        raise SystemExit(f'Check failed ({proc.returncode}); full output: {path.relative_to(ROOT)}')
    print(f'Passed in {time.monotonic() - started:.1f}s; log: {path.relative_to(ROOT)}', flush=True)
    return output


def main():
    EVIDENCE.mkdir(exist_ok=True)
    receipt = EVIDENCE / 'publication-check.json'
    # Never leave a previous success receipt masquerading as this invocation.
    result = {'checked_at_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'status': 'running', 'scope': 'complete library, final consumer, transitive axiom audit'}
    receipt.write_text(json.dumps(result, indent=2) + '\n')
    try:
        before = source_snapshot()
        pins = dependency_revisions()
        version = run(['lean', '--version'], 'toolchain.log').strip()
        if 'version 4.34.1,' not in version:
            raise RuntimeError(f'Unexpected Lean toolchain: {version}')
        run(['lake', '--rehash', 'build', 'ClusterSkeleton'], 'build.log')
        run(['lake', 'env', 'lean', 'verification/FullSkeletonConsumer.lean'], 'final-consumer.log')
        audit = run(['lake', 'env', 'lean', 'verification/AxiomAudit.lean'], 'axioms.log')
        audit_source = (EVIDENCE / 'AxiomAudit.lean').read_text()
        expected = re.findall(r'^#print axioms (\S+)', audit_source, re.M)
        entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit, re.S)
        no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", audit)
        reported = {name for name, _ in entries} | set(no_axioms)
        if set(expected) != reported or FINAL_TARGET not in reported:
            raise RuntimeError(f'Final axiom audit declaration mismatch: {set(expected) ^ reported}')
        for name, raw in entries:
            actual = {x.strip() for x in raw.split(',') if x.strip()}
            if actual - ALLOWED:
                raise RuntimeError(f'Unexpected axioms for {name}: {actual - ALLOWED}')
        audited_modules = dict(re.findall(r'AUDITED (ClusterSkeleton\.[\w.]+): (\d+) declarations', audit))
        sources = sorted((ROOT / 'ClusterSkeleton').rglob('*.lean'))
        accepted_library = json.loads((EVIDENCE / 'accepted-library.json').read_text())
        library_hashes = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sources}
        if library_hashes != accepted_library['source_sha256']:
            raise RuntimeError('Library differs from the accepted source manifest; review and update it explicitly')
        expected_modules = {'.'.join(p.relative_to(ROOT).with_suffix('').parts) for p in sources}
        if set(audited_modules) != expected_modules:
            raise RuntimeError(f'Module audit mismatch: {expected_modules ^ set(audited_modules)}')
        for source in sources:
            if re.search(r'^\s*(?:axiom|opaque)\b', source.read_text(), re.M):
                raise RuntimeError(f'Forbidden extra axiom/opaque declaration: {source.relative_to(ROOT)}')
        if dependency_revisions() != pins:
            raise RuntimeError('Dependency revisions changed during verification')
        if source_snapshot() != before:
            raise RuntimeError('Source changed during verification')
        result.update(status='passed', lean_version=version, dependency_commits=pins,
                      dependency_worktrees_clean=True, source_stability_verified=True,
                      final_target=FINAL_TARGET, final_target_status='proved',
                      accepted_library_commit=accepted_library['accepted_commit'],
                      accepted_library_source_equality=f'all {len(sources)} library files are byte-identical',
                      allowed_axioms=sorted(ALLOWED), audited_final_declarations=expected,
                      audited_modules={k: int(v) for k, v in audited_modules.items()},
                      source_sha256=before,
                      evidence_sha256={name: hashlib.sha256((EVIDENCE / name).read_bytes()).hexdigest()
                                       for name in ['toolchain.log', 'build.log', 'final-consumer.log', 'axioms.log']})
    except Exception as exc:
        result.update(status='failed', error=str(exc))
        raise
    except SystemExit as exc:
        result.update(status='failed', error=str(exc))
        raise
    finally:
        result['finished_at_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        receipt.write_text(json.dumps(result, indent=2) + '\n')
    print('FULL_GEOMETRIC_TARGET_VERIFIED')


if __name__ == '__main__':
    main()
