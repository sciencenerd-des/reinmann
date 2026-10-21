"""Verify the completed CI receipt at its exact historical proof commit."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'research/prime_spectral/verification_2026_10_21_ci_complete'
COMMIT = 'a3ca706ff023830d0bc9890d662caa9964b015f7'
RUN = 39563749171


def verify(check_current=False):
    manifest = json.loads((OUT / 'manifest.json').read_text())
    for name, expected in manifest.items():
        assert hashlib.sha256((OUT / name).read_bytes()).hexdigest() == expected, name
    result = json.loads((OUT / 'result.json').read_text())
    run = json.loads((OUT / 'run.json').read_text())
    expected_jobs = {'build-and-verify', 'xi-rectangle-deps', 'xi-rectangle-certificate'} | {
        f'xi-rectangle-shard ({i})' for i in range(11)}
    assert result['proof_commit'] == run['headSha'] == COMMIT
    assert result['run_id'] == RUN
    assert run['url'] == f'https://github.com/sciencenerd-des/reinmann/actions/runs/{RUN}'
    assert run['status'] == 'completed' and run['conclusion'] == 'success'
    jobs = {job['name']: job for job in run['jobs']}
    assert len(run['jobs']) == len(jobs) == 14 and set(jobs) == expected_jobs
    assert result['required_jobs'] == sorted(expected_jobs)
    assert all(j['status'] == 'completed' and j['conclusion'] == 'success'
               for j in jobs.values())
    for name in ['Refuse to rebuild any tile', 'Assemble the closed rectangle and PF43',
                 'Audit rectangle theorem dependencies and source', 'Audit finitePF43']:
        step = next(s for s in jobs['xi-rectangle-certificate']['steps'] if s['name'] == name)
        assert step['status'] == 'completed' and step['conclusion'] == 'success', name
    with zipfile.ZipFile(OUT / 'run-logs.zip') as archive:
        assert archive.testzip() is None
        logs = {p: archive.read(p).decode() for p in archive.namelist()
                if '/' not in p and p.endswith('.txt')}
        assert len(logs) == 14
        root_log = next(t for p, t in logs.items() if p.endswith('_build-and-verify.txt'))
        certificate_log = next(t for p, t in logs.items()
                               if p.endswith('_xi-rectangle-certificate.txt'))
    for name in ['CornerPowerSumCounterexample', 'FiniteHeightPFCalibration']:
        assert f'Built Reinmann.{name}' in root_log, name
    assert ('OK: all 2619 audited theorems depend only on '
            '[propext, Classical.choice, Quot.sound]') in root_log
    # Match the actual output line, not the shell's echoed grep command.
    audit = "'Reinmann.XiFinitePFCertified.finitePF43' depends on axioms: "
    audit += '[propext, Classical.choice, Quot.sound]'
    assert any(line.split('Z ', 1)[-1].strip() == audit
               for line in certificate_log.splitlines())
    assert result['root_audit_declarations'] == 2619
    assert result['local_Lean430_PF58_unconditional'] is False
    tree = subprocess.check_output(['git', 'rev-parse', COMMIT + '^{tree}'],
                                   cwd=ROOT, text=True).strip()
    assert tree == result['proof_tree']
    bindings = json.loads((OUT / 'proof_source_sha256.json').read_text())
    for path, expected in bindings.items():
        historical = subprocess.check_output(['git', 'show', f'{COMMIT}:{path}'], cwd=ROOT)
        assert hashlib.sha256(historical).hexdigest() == expected, path
        if check_current:
            assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, path
    print(f'Verified all 14 CI jobs at {COMMIT[:7]}, 2619 root audit declarations, '
          f'PF43 audit and {len(bindings)} historical source bindings.')
    if check_current:
        print('Current proof/configuration sources match that CI commit.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-current-sources', action='store_true')
    verify(parser.parse_args().check_current_sources)
