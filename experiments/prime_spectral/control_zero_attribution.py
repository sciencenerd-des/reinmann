"""Finite explicit-formula attribution; no negligible-infinite-tail assertion."""
from fractions import Fraction
import json
from pathlib import Path

from flint import acb, arb, ctx
from certified_weil import endpoints
from character_zero_atlas import OUT
from full_ground_fourier import sha256
from threshold_ground_gap import box

CONTROLS = [
    ('dh5', 'character5_label2_windows'),
    ('q13_label2', 'character13_label2_windows'),
    ('epstein5', 'epstein5_label0_windows'),
    ('q17_label3', 'character17_label3_windows'),
    ('q7_label3', 'character7_label3_windows'),
    ('q13_label6', 'character13_label6_windows'),
    ('epstein6', 'epstein6_label0_windows'),
]


def transform(z, length, coefficients, parity):
    """Transform in the stored basis exp(2*pi*i*n*(x+S/2)/S).

    Its real sine/cosine modes carry (-1)^n in centered physical coordinates.
    That phase cancels the (-1)^n from evaluating sinh at shifted integers.
    """
    w, pi = z*length/2, arb.pi()
    denominators = [w*w+(pi*n)**2 for n in range(1, len(coefficients)+(parity == 'odd'))]
    if w.contains(0) or any(d.contains(0) for d in denominators):
        # Entire sinc representation at removable rational-form poles.
        base = (acb(0, 1)*w).sinc()
        value = coefficients[0]*base if parity == 'even' else acb(0)
        start = 1 if parity == 'even' else 0
        for j in range(start, len(coefficients)):
            n = j if parity == 'even' else j+1
            plus = (acb(0, 1)*(w+acb(0, pi*n))).sinc()
            minus = (acb(0, 1)*(w-acb(0, pi*n))).sinc()
            value += (-1)**n*coefficients[j]*(plus+minus)/arb(2).sqrt() if parity == 'even' else (-1)**n*coefficients[j]*(plus-minus)/acb(0, arb(2).sqrt())
        return length.sqrt()*value
    if parity == 'even':
        value = coefficients[0]/w
        for n in range(1, len(coefficients)):
            value += arb(2).sqrt()*coefficients[n]*w/denominators[n-1]
        return length.sqrt()*w.sinh()*value
    value = sum((coefficients[n-1]*pi*n/denominators[n-1]
                 for n in range(1, len(coefficients)+1)), acb(0))
    return -(2*length).sqrt()*w.sinh()*value


def attribute(name, atlas_path, trial_path):
    atlas = json.loads(atlas_path.read_text())
    data = json.loads(trial_path.read_text())
    length = arb(data['C']).log()
    records = []
    for sector in data['sectors']:
        if 'normalized_full_form' not in sector:
            continue
        parity = sector['parity']
        coefficients = [arb(x) for x in sector['exact_trial_coefficients']]
        norm = sum((x*x for x in coefficients), arb(0)).sqrt()
        coefficients = [x/norm for x in coefficients]
        sign = 1 if parity == 'even' else -1
        lines = arb(0)
        for disk in atlas['critical_line_disks']:
            gamma = box(disk['imag'])+arb(0, arb(disk['radius']))
            value = transform(acb(0, gamma), length, coefficients, parity)
            if parity == 'even' and not value.imag.contains(0) or parity == 'odd' and not value.real.contains(0):
                raise ArithmeticError('real parity transform check failed')
            lines += 2*(value.real if parity == 'even' else value.imag)**2
        off, total = [], lines
        for disk in atlas['right_off_line_zeros']:
            beta = box(disk['real'])+arb(0, arb(disk['radius']))
            gamma = box(disk['imag'])+arb(0, arb(disk['radius']))
            value = transform(acb(beta-arb('1/2'), gamma), length, coefficients, parity)
            contribution = 4*sign*(value*value).real
            total += contribution
            off.append({'beta': endpoints(beta), 'gamma': endpoints(gamma),
                        'offset': endpoints(beta-arb('1/2')),
                        'quartet_contribution': endpoints(contribution),
                        'negative_finite_contribution_certified': bool(contribution < 0)})
        negative = [j for j, r in enumerate(off) if r['negative_finite_contribution_certified']]
        dominant = min(negative, key=lambda j: float(box(off[j]['quartet_contribution']).mid())) if negative else None
        q = box(sector['normalized_full_form'])
        record = {'parity': parity, 'trial_dimension': len(coefficients),
                  'geometric_full_quotient': endpoints(q), 'finite_line_sum': endpoints(lines),
                  'off_line_quartets': off, 'finite_total': endpoints(total),
                  'finite_total_negative_certified': bool(total < 0),
                  'geometric_minus_finite_sum': endpoints(q-total),
                  'dominant_negative_quartet_index': dominant,
                  'dominance_over_other_enclosed_quartets_certified':
                      dominant is not None and all(
                          box(off[dominant]['quartet_contribution']) < box(other['quartet_contribution'])
                          for j, other in enumerate(off) if j != dominant),
                  'scope': 'Enclosed contributions from the complete finite atlas only. The difference from the geometric value is not an independent analytic upper bound proving the omitted tail negligible. Causal attribution and global tail dominance remain evidence.'}
        records.append(record)
        chosen = off[dominant] if dominant is not None else None
        print(name, parity, 'negative quartet gamma', box(chosen['gamma']).str(10) if chosen else None,
              'finite sum', total.str(10), 'geometric', q.str(10), flush=True)
    return {'name': name, 'atlas_height': atlas['height'], 'C': data['C'], 'modes': data['modes'],
            'witnesses': records, 'input_sha256': {str(p): sha256(p) for p in [atlas_path, trial_path]}}


def run():
    results = []
    with ctx.workprec(2048):
        for name, folder in CONTROLS:
            summary_path = OUT/folder/'search_N192_2048bits.json'
            search = json.loads(summary_path.read_text())
            high = search['negative_certificate_C']
            chosen = next(r for r in reversed(search['records']) if r['C'] == high and r['status'] == 'negative_full_form_trial')
            results.append(attribute(name, OUT/f'{name}_refined_atlas.json', Path(chosen['file'])))
    result = {'status': 'finite_atlas_quartet_attribution_enclosed_no_negligible_tail_claim',
              'controls': results,
              'source_sha256': {'control_zero_attribution.py': sha256(Path(__file__))},
              'scope': 'Finite-sum attribution evidence, not a proof that the displayed quartet alone causes the full negative form or a universal detection law.'}
    (OUT/'zero_attribution.json').write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    run()
