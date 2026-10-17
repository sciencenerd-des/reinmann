"""Bind the Jacobi/evaluator round while retaining the prior scientific closure."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'research/prime_spectral/verification_2026_10_18_jacobi'
PREVIOUS = ROOT / 'research/prime_spectral/verification_2026_10_17_formal_A/manifest.json'
MANIFEST = OUT / 'manifest.json'
MUTABLE = {'README.md', 'Reinmann.lean', 'Reinmann/AxiomAudit.lean'}
MODULES = ['ToeplitzComplement', 'ToeplitzComplementSigned', 'SplitPairCauchyTail',
           'XiFiniteTheta', 'EnclosureRules']


def sha(p):
    with p.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def run(record=False):
    previous = json.loads(PREVIOUS.read_text())
    bound = {}
    for name, h in previous['artifacts_sha256'].items():
        p = ROOT / name
        if name in MUTABLE:
            if sha(OUT / 'historical_aba0f38' / name) != h:
                raise ValueError('historical baseline mismatch: ' + name)
        elif sha(p) != h:
            raise ValueError('prior scientific artifact changed: ' + name)
        bound[p] = sha(p)
    names = []
    audit = (ROOT / 'Reinmann/AxiomAudit.lean').read_text()
    for module in MODULES:
        p = ROOT / 'Reinmann' / (module + '.lean')
        source = p.read_text()
        namespace = re.search(r'^namespace (\S+)', source, re.M).group(1)
        for name in re.findall(r'^(?:@\[[^\n]*\]\s*)?theorem\s+(\w+)', source, re.M):
            full = namespace + '.' + name
            if '#print axioms ' + full not in audit:
                raise ValueError('new theorem missing from audit: ' + full)
            names.append(full)
        bound[p] = sha(p)
    if len(names) != 28:
        raise ValueError('unexpected public theorem inventory')
    validation = json.loads((OUT / 'validation.json').read_text())
    for item in validation['checks']:
        if item['exit_code'] != 0:
            raise ValueError('failed final check: ' + item['name'])
        p = ROOT / item['log']
        if sha(p) != item['sha256']:
            raise ValueError('validation log changed: ' + item['name'])
        if 'error:' in p.read_text() or 'build failed' in p.read_text():
            raise ValueError('error in final validation log: ' + item['name'])
    for name, h in validation['source_sha256'].items():
        if sha(ROOT / name) != h:
            raise ValueError('source differs from validated version: ' + name)
    log = (OUT / 'axiom_audit.log').read_text()
    if 'all 313 audited theorems' not in log or 'AXIOM-CLEAN: 0 sorry, 0 custom axioms.' not in log:
        raise ValueError('missing successful final axiom audit')
    for p in OUT.rglob('*'):
        if p.is_file() and p != MANIFEST:
            bound[p] = sha(p)
    for name in ['research/prime_spectral/FORMAL_TARGET_A_JACOBI_AND_EVALUATOR_2026_10_18.md',
                 'research/prime_spectral/DENSITY_AND_EXACT_INTERPOLATION_2026_10_18.md',
                 'experiments/prime_spectral/verify_jacobi_round.py',
                 'scripts/reassemble_dh_supplement.py']:
        p = ROOT / name
        bound[p] = sha(p)
    bound[PREVIOUS] = sha(PREVIOUS)
    result = {
        'status': 'jacobi_bridge_and_evaluator_components_verified',
        'baseline_commit': 'aba0f38', 'new_public_theorems': names,
        'total_audited_theorems': 313, 'sorry': 0, 'custom_axioms': 0,
        'declared_updated_files': sorted(MUTABLE),
        'prior_scientific_artifacts_unchanged': True,
        'scope': 'Original-coefficient finite-product Jacobi bridge and sign oscillation; '
                 'Cauchy coefficient component; actual finite-theta tails; quadrature, '
                 'variation and closed-grid coverage rules. No completed genus-zero '
                 'extension, actual Xi per-tile certificate, discharged low-zero input, '
                 'new logarithmic detection theorem, RH proof or publication.',
        'artifacts_sha256': {str(p.relative_to(ROOT)): h for p, h in sorted(bound.items())},
    }
    if record:
        if MANIFEST.exists():
            raise FileExistsError('manifest exists; inspect differences rather than overwrite')
        MANIFEST.write_text(json.dumps(result, indent=2) + '\n')
    elif json.loads(MANIFEST.read_text()) != result:
        raise ValueError('round differs from manifest')
    print(result['status'], len(bound), 'bound artifacts;', len(names), 'new public theorems')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--record', action='store_true')
    run(parser.parse_args().record)
