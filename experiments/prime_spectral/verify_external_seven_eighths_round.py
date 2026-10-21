"""Check the completed external proof packet and its historical predecessors."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'research/prime_spectral/verification_2026_10_21_external_seven_eighths'
sys.path.insert(0, str(ROOT/'bridges/openai-seven-eighths'))
from finalize_minimal_replay import PIN, TOOLCHAIN, verify_packet


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify(record=False):
    verify_packet(OUT)
    result = json.loads((OUT/'result.json').read_text())
    control = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())['finite_strengthening_controls'][0]
    assert control['classification'] == 'finite_strengthening_external_proof_replayed_separate_toolchain'
    replay = control['external_replay']
    assert replay['upstream_commit'] == PIN and replay['toolchain'] == TOOLCHAIN
    assert replay['receipt_sha256'] == sha(ROOT/replay['receipt'])
    assert replay['status'] == result['status'] and replay['source_modules'] == 2943
    assert replay['local_Lean430_PF58_unconditional'] is False
    for name in ['Reinmann.lean', 'Reinmann/AxiomAudit.lean']:
        assert (ROOT/name).read_bytes() == subprocess.check_output(['git', 'show', f'91c034d:{name}'], cwd=ROOT)
    assert 'QuasiRiemannHypothesisSevenEighths' in (ROOT/'Reinmann/XiFinitePFCertified.lean').read_text()
    with tempfile.TemporaryDirectory(prefix='rh-external-replay-check-') as tmp:
        receipt = Path(tmp)/'replay.json'
        subprocess.run(['python3', 'experiments/prime_spectral/replay_seven_eighths_predecessors.py',
                        '--output', str(receipt)], cwd=ROOT, check=True, stdout=subprocess.PIPE)
        assert json.loads(receipt.read_text()) == json.loads((OUT/'predecessor_replay.json').read_text())
    owned = ['research/RH_DH_DISCRIMINATOR_REGISTER.json', 'research/RH_DH_DISCRIMINATOR_REGISTER.md',
             'bridges/openai-seven-eighths/finalize_minimal_replay.py',
             'experiments/prime_spectral/replay_seven_eighths_predecessors.py',
             'experiments/prime_spectral/verify_external_seven_eighths_round.py',
             'research/prime_spectral/EXTERNAL_SEVEN_EIGHTHS_REPLAY_2026_10_21.md']
    bindings = {name: sha(ROOT/name) for name in owned}
    bindings.update({str(path.relative_to(ROOT)): sha(path) for path in OUT.rglob('*')
                     if path.is_file() and path.name != 'round_manifest.json'})
    receipt = dict(status='external_seven_eighths_replay_round_verified',
                   upstream_commit=PIN, toolchain=TOOLCHAIN,
                   fresh_source_modules=2943, OAI_source_modules=2924,
                   local_Lean430_PF58_unconditional=False, RH_proved=False,
                   artifacts_sha256=bindings)
    path = OUT/'round_manifest.json'
    if record:
        with path.open('x') as stream:
            stream.write(json.dumps(receipt, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == receipt
    print('Verified external 7/8 exact contract, two standard-axiom reports and historical chain;',
          len(bindings), 'bindings. Main Lean 4.30 PF58 retains its named external input.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', action='store_true')
    verify(parser.parse_args().record)
