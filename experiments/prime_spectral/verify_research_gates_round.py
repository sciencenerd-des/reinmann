"""Replay the DH-first round without rewriting historical proof manifests."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

from verify_xi_rectangle import strip_comments

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT/'research/prime_spectral/verification_2026_10_20_research_gates'
OWNED = [
    'AGENTS.md', 'Reinmann/CornerPowerSumCounterexample.lean',
    'Reinmann/FiniteHeightPFCalibration.lean',
    'research/RH_DH_DISCRIMINATOR_REGISTER.json',
    'research/RH_DH_DISCRIMINATOR_REGISTER.md',
    'bridges/openai-seven-eighths/SevenEighths.lean',
    'bridges/openai-seven-eighths/replay.py',
    'bridges/openai-seven-eighths/README.md',
]
OWNED += ['experiments/prime_spectral/'+n+'.py' for n in [
    'check_dh_research_gate', 'replay_frozen_research_checkpoints',
    'weil_endpoint_jump_probe', 'weil_endpoint_jet_probe',
    'prepare_formal_rectangle_release', 'verify_research_gates_round']]
OWNED += ['research/prime_spectral/'+n+'_2026_10_20.md' for n in [
    'QUASI_RH_EXTRACTION_BARRIER', 'WEIL_ENDPOINT_JUMP_FACTOR',
    'CORNER_POWER_SUM_OBSTRUCTION', 'FINITE_HEIGHT_PF_PLAN',
    'RESEARCH_GATES_AND_ARITHMETIC_SCOPE']]


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def check(record=False):
    subprocess.run(['python3', 'experiments/prime_spectral/check_dh_research_gate.py'],
                   cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix='rh-gate-check-') as tmp:
        replay = Path(tmp)/'replay.json'
        result = subprocess.run(['python3', 'experiments/prime_spectral/replay_frozen_research_checkpoints.py',
                                 '--output', str(replay)], cwd=ROOT, check=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert json.loads(replay.read_text()) == json.loads((OUT/'historical_replay.json').read_text())
        assert b'825 theorem audits and 146 bindings' in result.stdout
    expected = {
        'Reinmann.CornerPowerSumCounterexample.powerSum_ge_third',
        'Reinmann.CornerPowerSumCounterexample.shift_two_rank_three',
        'Reinmann.CornerPowerSumCounterexample.not_finitePF_three',
        'Reinmann.FiniteHeightPFCalibration.angleBound_of_two_bands',
        'Reinmann.FiniteHeightPFCalibration.finitePF97_of_low_height_width'}
    audit = (OUT/'axioms.log').read_text()
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
    assert len(rows) == 5 and {n for n, _ in rows} == expected
    assert all(set(a.replace(',', ' ').split()) <= {'propext', 'Classical.choice', 'Quot.sound'}
               for _, a in rows)
    for name in OWNED:
        if name.endswith('.lean'):
            assert not re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom)\b',
                                 strip_comments((ROOT/name).read_text())), name
    commands = json.loads((OUT/'commands.json').read_text())
    assert len(commands) == 5 and all(c['exit_code'] == 0 for c in commands)
    assert all('error:' not in (OUT/c['log']).read_text() for c in commands)
    guard = (OUT/'root_guard.log').read_text()
    assert 'all 2608 audited theorems' in guard and 'AXIOM-CLEAN:' in guard
    for kind, script in [('jump', 'weil_endpoint_jump_probe'), ('jet', 'weil_endpoint_jet_probe')]:
        data = json.loads((OUT/f'endpoint_{kind}_probe.json').read_text())
        assert data['status'] == 'floating_finite_band_diagnostic_not_certificate'
        assert data['source_sha256'] == digest(ROOT/f'experiments/prime_spectral/{script}.py')
        assert [r['control'] for r in data['rows']] == ['DH']*4+['zeta']*4
        assert all(r['max_quadrature_difference'] < 1e-10 for r in data['rows'])
        assert all(abs(r['finite_band_checks'][-1]['ratio']-1) < .005 for r in data['rows'])
    # Exact optimizer of the stated bound, not an arithmetic theorem premise.
    assert Fraction(2, 7)*Fraction(5, 12)-Fraction(5, 7)*Fraction(1, 6) == 0
    assert Fraction(2, 7)*Fraction(1, 2)+Fraction(5, 7) == Fraction(6, 7)
    visual = json.loads((OUT/'paper_visual_review.json').read_text())
    assert visual['pages_rendered_and_inspected'] == 7
    assert not visual['external_human_review_completed']
    assert visual['pdf_sha256'] == digest(OUT/'paper_candidate/main.pdf')
    assert visual['tex_sha256'] == digest(OUT/'paper_candidate/main.tex')
    assert b'hosted rectangle check pending' in (OUT/'paper_candidate/main.tex').read_bytes()
    assert 'Release gate closed' in (OUT/'release_gate_closed.log').read_text()
    # These are historical pending receipts, never current publication evidence.
    ci = json.loads((OUT/'ci_snapshot_pending.json').read_text())
    assert ci['headSha'] == '150537bf1d94eced1c22db7660f9c32936372831'
    assert ci['status'] == 'in_progress' and ci['conclusion'] == ''
    bound = {name: digest(ROOT/name) for name in OWNED}
    bound.update({str(p.relative_to(ROOT)): digest(p) for p in OUT.rglob('*')
                  if p.is_file() and p.name != 'manifest.json'})
    receipt = dict(status='DH_first_research_round_verified', new_standard_axiom_theorems=5,
                   numeric_diagnostics_are_certificates=False,
                   height_32_certificate_proved=False, external_seven_eighths_adapter_built=False,
                   hosted_rectangle_gate_status_at_snapshot='pending',
                   paper_status='unpublished_revision_candidate', artifacts_sha256=bound)
    path = OUT/'manifest.json'
    if record:
        with path.open('x') as f:
            f.write(json.dumps(receipt, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == receipt, 'Round differs from immutable receipt'
    print('Verified DH gate, five new theorem audits, two finite-band probes and frozen parent replay;',
          len(bound), 'bindings. No new window/height certificate or publication claimed.')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--record', action='store_true')
    check(p.parse_args().record)
