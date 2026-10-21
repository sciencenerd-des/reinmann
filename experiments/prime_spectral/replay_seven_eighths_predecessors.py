"""Replay the preceding coverage receipt with its historical pending register."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from replay_frozen_research_checkpoints import link_children

ROOT = Path(__file__).resolve().parents[2]
PIN = '91c034d'
SAVED = ROOT/'research/prime_spectral/verification_2026_10_21_external_seven_eighths/historical_91c034d'
FILES = ['research/RH_DH_DISCRIMINATOR_REGISTER.json', 'research/RH_DH_DISCRIMINATOR_REGISTER.md']


def replay(output):
    bindings = {}
    for relative in FILES:
        data = (SAVED/relative).read_bytes()
        assert data == subprocess.check_output(['git', 'show', f'{PIN}:{relative}'], cwd=ROOT)
        bindings[relative] = hashlib.sha256(data).hexdigest()
    with tempfile.TemporaryDirectory(prefix='rh-seven-eighths-predecessors-') as tmp:
        overlay = Path(tmp)
        for path in ROOT.iterdir():
            target = overlay/path.name
            if path.name == 'experiments':
                link_children(path, target, {'prime_spectral': {}})
            elif path.name == 'research':
                link_children(path, target, {})
            else:
                target.symlink_to(path, target_is_directory=path.is_dir())
        for relative in FILES:
            target = overlay/relative
            assert target.is_symlink()
            target.unlink()
            target.write_bytes((SAVED/relative).read_bytes())
        run = subprocess.run(['python3', 'experiments/prime_spectral/verify_ci_coverage_round.py'],
                             cwd=overlay, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(run.stdout.decode(), end='')
        if run.returncode:
            raise SystemExit(run.returncode)
    result = dict(status='seven_eighths_predecessors_replayed_with_pending_register_snapshot',
                  historical_commit=PIN, historical_register_sha256=bindings,
                  verifier_output_sha256=hashlib.sha256(run.stdout).hexdigest(),
                  scope='Historical receipt replay only. External proof packet verified separately.')
    with Path(output).open('x') as stream:
        stream.write(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    replay(parser.parse_args().output)
