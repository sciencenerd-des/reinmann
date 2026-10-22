"""Replay earlier immutable receipts against their unchanged pre-band sources."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from replay_frozen_research_checkpoints import link_children

ROOT = Path(__file__).resolve().parents[2]
PIN = 'bd12b0e0279f6d0edc5d1fa930ef5cbf34c5377b'
FILES = ['Reinmann.lean', 'Reinmann/AxiomAudit.lean', 'lakefile.toml',
         '.github/workflows/ci.yml', 'Reinmann/FiniteHeightPFCalibration.lean',
         'Reinmann/XiFinitePFCertified.lean', 'README.md',
         'research/pseudo_hermitian/RESEARCH_OBJECTIVE.md',
         'research/RH_DH_DISCRIMINATOR_REGISTER.json', 'research/RH_DH_DISCRIMINATOR_REGISTER.md']


def replay(output):
    historical = {name: subprocess.check_output(['git', 'show', f'{PIN}:{name}'], cwd=ROOT)
                  for name in FILES}
    with tempfile.TemporaryDirectory(prefix='rh-finite-band-predecessors-') as tmp:
        overlay = Path(tmp)
        for path in ROOT.iterdir():
            target = overlay / path.name
            if path.name == 'experiments':
                link_children(path, target, {'prime_spectral': {}})
            elif path.name == 'Reinmann':
                link_children(path, target, {})
            elif path.name == 'research':
                link_children(path, target, {'pseudo_hermitian': {}})
            elif path.name == '.github':
                link_children(path, target, {'workflows': {}})
            else:
                target.symlink_to(path, target_is_directory=path.is_dir())
        for relative, data in historical.items():
            target = overlay / relative
            assert target.is_symlink()
            target.unlink()
            target.write_bytes(data)
        logs = []
        for script in ['verify_external_seven_eighths_round.py', 'verify_ci_complete_2026_10_21.py']:
            result = subprocess.run(['python3', 'experiments/prime_spectral/'+script], cwd=overlay,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            print(result.stdout.decode(), end='')
            if result.returncode:
                raise SystemExit(result.returncode)
            logs.append({'script': script, 'output_sha256': hashlib.sha256(result.stdout).hexdigest()})
    receipt = {'status': 'pre_band_immutable_chain_replayed', 'historical_commit': PIN,
               'historical_files_sha256': {n: hashlib.sha256(b).hexdigest() for n, b in historical.items()},
               'verifiers': logs, 'scope': 'Historical verification only; no new box proof claimed.'}
    with output.open('x') as stream:
        stream.write(json.dumps(receipt, indent=2)+'\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    replay(parser.parse_args().output)
