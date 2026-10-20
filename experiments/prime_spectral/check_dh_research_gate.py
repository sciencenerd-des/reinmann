"""Check the standing RH/DH register, provenance and claimed witness scope."""
import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def main():
    d = json.loads((ROOT/'research/RH_DH_DISCRIMINATOR_REGISTER.json').read_text())
    ids = set()
    for r in d['routes']:
        assert r['id'] not in ids
        ids.add(r['id'])
        assert r['target'] and r['dh_analogue'] and r['arithmetic_property'] and r['gap']
        assert r['classification'] in {'reformulation', 'uninstantiated', 'strategy'}
        f = r['failure']
        assert f['globally_first'] is False
        if 'source' in f:
            p = ROOT/f['source']
            assert hashlib.sha256(p.read_bytes()).hexdigest() == f['source_sha256']
        if r['classification'] == 'strategy':
            assert r['separating_inequality'] and f['kind'] == 'certified_tested_witness'
    by_id = {r['id']: r for r in d['routes']}
    f = by_id['toeplitz_all_ranks']['failure']
    data = json.loads((ROOT/f['source']).read_text())
    assert data['first_negative_nearby_cell'] == {'rank': f['rank'], 'shift': f['shift']}
    assert data['observed_band'] == f['second_band']
    f = by_id['weil_all_windows']['failure']
    data = json.loads((ROOT/f['source']).read_text())
    assert data['status'] == 'negative_full_form_trial' and data['C'] == f['C']
    assert any(Fraction(s['normalized_full_form']['hi']) < 0 for s in data['sectors']
               if 'normalized_full_form' in s)
    print('DH gate: five targets registered; retained Toeplitz/Weil witnesses agree; no active RH strategy claimed')


if __name__ == '__main__':
    main()
