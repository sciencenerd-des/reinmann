"""Capture a complete successful finite-band CI gate, or verify its saved packet."""
import argparse
import ast
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[2]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git_blob(commit, path):
    return subprocess.check_output(['git', 'show', commit+':'+path], cwd=ROOT)


def check_gate(run, commit, ranks):
    expected = {'build-and-verify', 'xi-rectangle-deps', 'xi-rectangle-certificate'}
    expected |= {f'xi-rectangle-shard ({i})' for i in range(11)}
    for rank in ranks:
        expected |= {f'xi-band{rank}-shard ({i})' for i in range(3 if rank == 58 else 17)}
    assert run['headSha'] == commit
    assert run['status'] == 'completed' and run['conclusion'] == 'success', 'CI gate not successful'
    assert len(run['jobs']) == len(expected) and {j['name'] for j in run['jobs']} == expected
    assert all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in run['jobs'])
    final = next(j for j in run['jobs'] if j['name'] == 'xi-rectangle-certificate')
    for rank in ranks:
        name = f'Audit finite-band PF{rank} and every generated theorem'
        assert next(s for s in final['steps'] if s['name'] == name)['conclusion'] == 'success'
    assert next(s for s in final['steps'] if s['name'] == 'Refuse to rebuild any tile')['conclusion'] == 'success'


def check_audit(directory, commit, rank):
    result = json.loads((directory/'result.json').read_text())
    assert result['status'] == 'actual_finite_band_kernel_audit_succeeded'
    assert result['proof_commit'] == commit and result['rank'] == rank
    assert result['finitePF_unconditional'] and result['standard_axioms_only']
    assert result['RH_proved'] is False
    log = (directory/'audit.log').read_bytes()
    assert sha(log) == result['audit_log_sha256']
    text = re.sub(r'\n\s+', ' ', log.decode())
    assert 'error:' not in text
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
    empty = re.findall(r"'([^']+)' does not depend on any axioms", text)
    count = int(re.search(r'BAND_AUDIT_COUNT (\d+)', text).group(1))
    assert len(found)+len(empty) == count+2 == result['theorem_declarations_audited']
    assert len({n for n, _ in found} | set(empty)) == count+2
    assert all({v.strip() for v in a.split(',')} <= ALLOWED for _, a in found)
    for name in [f'Reinmann.XiBand{rank}.finitePF{rank}',
                 f'Reinmann.XiFinitePFCertified.finitePF{rank}']:
        assert name in {n for n, _ in found}
    for path, expected in result['source_sha256'].items():
        assert sha(git_blob(commit, path)) == expected, path
    code = ast.parse(git_blob(commit, 'experiments/prime_spectral/verify_finite_band.py').decode())
    function = next(n for n in code.body if isinstance(n, ast.FunctionDef) and n.name == 'verify')
    assignment = next(n for n in ast.walk(function) if isinstance(n, ast.Assign)
                      and any(isinstance(t, ast.Name) and t.id == 'source' for t in n.targets))
    assert isinstance(assignment.value, ast.JoinedStr)
    parameters = {'library': f'XiBand{rank}', 'rank': str(rank)}
    parts = []
    for part in assignment.value.values:
        if isinstance(part, ast.Constant):
            assert isinstance(part.value, str)
            parts.append(part.value)
        else:
            assert isinstance(part, ast.FormattedValue) and isinstance(part.value, ast.Name)
            assert part.conversion == -1 and part.format_spec is None
            parts.append(parameters[part.value.id])
    source = ''.join(parts)
    assert (directory/'Audit.lean').read_text() == source
    return result


def verify(directory):
    manifest = json.loads((directory/'manifest.json').read_text())
    for name, expected in manifest.items():
        assert sha((directory/name).read_bytes()) == expected, name
    result = json.loads((directory/'result.json').read_text())
    run = json.loads((directory/'run.json').read_text())
    check_gate(run, result['proof_commit'], result['ranks'])
    for rank in result['ranks']:
        audit = check_audit(directory/f'PF{rank}', result['proof_commit'], rank)
        assert audit['theorem_declarations_audited'] == result['band_audit_counts'][str(rank)]
    bindings = json.loads((directory/'proof_source_sha256.json').read_text())
    for path, expected in bindings.items():
        assert sha(git_blob(result['proof_commit'], path)) == expected, path
    with zipfile.ZipFile(directory/'run-logs.zip') as archive:
        assert archive.testzip() is None
        assert len([n for n in archive.namelist() if '/' not in n and n.endswith('.txt')]) == len(run['jobs'])
    print('Verified complete finite-band CI packet:', result['proof_commit'],
          result['ranks'], len(run['jobs']), 'successful jobs;', len(bindings), 'source bindings.')


def capture(run_id, commit, ranks, output):
    assert not output.exists(), output
    raw = subprocess.check_output(['gh', 'run', 'view', str(run_id), '--json',
                                   'status,conclusion,headSha,jobs,url'], cwd=ROOT)
    run = json.loads(raw)
    # Refuse a pending/failed gate before creating any release-like evidence.
    check_gate(run, commit, ranks)
    with tempfile.TemporaryDirectory(prefix='finite-band-ci-capture-') as tmp:
        stage = Path(tmp)
        counts = {}
        for rank in ranks:
            directory = stage/f'PF{rank}'
            subprocess.run(['gh', 'run', 'download', str(run_id), '-n', f'xi-band{rank}-audit',
                            '-D', str(directory)], cwd=ROOT, check=True)
            counts[str(rank)] = check_audit(directory, commit, rank)['theorem_declarations_audited']
        logs = subprocess.check_output(['gh', 'api',
            f'repos/sciencenerd-des/reinmann/actions/runs/{run_id}/logs'], cwd=ROOT)
        with zipfile.ZipFile(io.BytesIO(logs)) as archive:
            assert archive.testzip() is None
        (stage/'run-logs.zip').write_bytes(logs)
        (stage/'run.json').write_text(json.dumps(run, indent=2)+'\n')
        paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', commit],
                                        cwd=ROOT, text=True).splitlines()
        extras = {'lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
                  '.github/workflows/ci.yml', 'scripts/verify_axiom_clean.sh'}
        paths = [p for p in paths if p.endswith('.lean') or p in extras]
        bindings = {p: sha(git_blob(commit, p)) for p in paths}
        (stage/'proof_source_sha256.json').write_text(json.dumps(bindings, indent=2)+'\n')
        result = {'status': 'complete_finite_band_CI_gate_verified', 'run_id': run_id,
                  'proof_commit': commit, 'run_url': run['url'], 'ranks': ranks,
                  'successful_jobs': len(run['jobs']), 'band_audit_counts': counts,
                  'standard_axioms_only': True, 'RH_proved': False,
                  'lean_toolchain': git_blob(commit, 'lean-toolchain').decode().strip(),
                  'scope': 'Finite-width certificates; critical-line zeros above 14.1 are allowed.'}
        (stage/'result.json').write_text(json.dumps(result, indent=2)+'\n')
        manifest = {str(p.relative_to(stage)): sha(p.read_bytes()) for p in stage.rglob('*') if p.is_file()}
        (stage/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
        verify(stage)
        import shutil
        output.parent.mkdir(parents=True, exist_ok=True)
        shutil.copytree(stage, output)
    verify(output)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', type=Path)
    parser.add_argument('--run', type=int)
    parser.add_argument('--commit')
    parser.add_argument('--ranks', type=int, nargs='+', choices=(58, 97))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.verify:
        verify(args.verify)
    else:
        assert args.run and args.commit and args.ranks and args.output
        capture(args.run, args.commit, args.ranks, args.output)
