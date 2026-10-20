"""Replay immutable proof checkpoints using exact historical root-file overlays.

This checks the old receipts without changing the current source or weakening
any hash. Current proof builds/audits must be checked separately.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
PIN = 'bdbc051'
FROZEN = ROOT / 'research/prime_spectral/verification_2026_10_20_ci_coverage/historical_bdbc051'
CHANGED = ['Reinmann.lean', 'Reinmann/AxiomAudit.lean', '.github/workflows/ci.yml']


def link_children(source, target, recurse):
    target.mkdir()
    for p in source.iterdir():
        if p.name == '__pycache__':
            continue
        q = target / p.name
        if p.name in recurse:
            link_children(p, q, recurse[p.name])
        elif p.is_file() and p.suffix == '.py':
            shutil.copy2(p, q)
        else:
            q.symlink_to(p, target_is_directory=p.is_dir())


def replay(output):
    bindings = {}
    for relative in CHANGED:
        saved = (FROZEN / relative).read_bytes()
        actual = subprocess.check_output(['git', 'show', f'{PIN}:{relative}'], cwd=ROOT)
        assert saved == actual, relative
        bindings[relative] = hashlib.sha256(saved).hexdigest()
    with tempfile.TemporaryDirectory(prefix='rh-frozen-replay-') as tmp:
        overlay = Path(tmp)
        for p in ROOT.iterdir():
            q = overlay / p.name
            if p.name == 'experiments':
                link_children(p, q, {'prime_spectral': {}})
            elif p.name == 'Reinmann':
                link_children(p, q, {})
            elif p.name == '.github':
                link_children(p, q, {'workflows': {}})
            else:
                q.symlink_to(p, target_is_directory=p.is_dir())
        for relative in CHANGED:
            p = overlay / relative
            assert p.is_symlink()
            p.unlink()
            p.write_bytes((FROZEN / relative).read_bytes())
        p = subprocess.run(['python3', 'experiments/prime_spectral/verify_pnt_hadamard_backport.py'],
                           cwd=overlay, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(p.stdout.decode(), end='')
        if p.returncode:
            raise SystemExit(p.returncode)
    receipt = dict(status='immutable_checkpoint_chain_replayed_with_historical_root_files',
                   historical_commit=PIN, historical_root_sha256=bindings,
                   scope='Receipt replay only. Current-root build and axiom audit are separate.',
                   verifier_output_sha256=hashlib.sha256(p.stdout).hexdigest())
    Path(output).write_text(json.dumps(receipt, indent=2)+'\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', required=True)
    replay(p.parse_args().output)
