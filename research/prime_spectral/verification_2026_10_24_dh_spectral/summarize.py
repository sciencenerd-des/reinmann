"""Summarize retained finite diagnostics; run from the repository root."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
names = ['dh_rank32_64_corrected.json', 'dh_rank96_refined.json',
         'dh_precision_replay.json', 'dh_C35_rank128.json']
records = {}
for name in names:
    for r in json.loads((ROOT/name).read_text())['records']:
        records[r['C'], r['modes']] = dict(r, input_receipt=name)

rows = []
for key, r in sorted(records.items()):
    parity = r.get('global_ground_parity',
                   'even' if r['ground_is_even_midpoint_diagnostic'] else 'odd')
    rows.append({'C': r['C'], 'modes': r['modes'], 'ground_parity': parity,
                 'lowest_even': r['even_lowest'][0], 'lowest_odd': r['odd_lowest'][0],
                 'candidate_ground_overlap': r['candidate_ground_overlap'] if parity == 'even' else '0',
                 'candidate_residual_over_global_gap': r['candidate_residual_over_global_gap'],
                 'global_second_minus_candidate_rayleigh': r['global_second_minus_candidate_rayleigh'],
                 'candidate_reflection_defect_ratio': r['candidate']['reflection_defect_ratio'],
                 'input_receipt': r['input_receipt']})

certificate_names = ['finite_C31_N64_current_certificate.json',
                     'finite_C35_N64_parity_certificate.json',
                     'finite_C35_N96_parity_certificate.json',
                     'finite_C35_N128_parity_certificate.json']
certificates = []
for name in certificate_names:
    d = json.loads((ROOT/name).read_text())
    certificates.append({'receipt': name, 'C': d['C'], 'modes': d['modes'],
                         'ground_parity': d['ground_parity'], 'ground_sign': d['ground_sign']})
    assert d['ground_sign'] == 'negative'
    assert Fraction(d['global_gap']['lo']) > 0

summary = {'status': 'finite_DH_control_instantiated_no_arithmetic_discriminator',
           'rows': rows, 'certified_finite_spectra': certificates,
           'limitations': ['Projected floating candidate residuals only.',
                           'Exact prolate and full-operator comparison not certified.',
                           'No C~13.6 transition or minimal failure window established.',
                           'Rank-dependent ground parity; no all-rank limit established.'],
           'input_sha256': {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest()
                            for name in names+certificate_names}}
if (ROOT/'summary.json').exists():
    assert json.loads((ROOT/'summary.json').read_text()) == summary
else:
    with (ROOT/'summary.json').open('x') as stream:
        stream.write(json.dumps(summary, indent=2)+'\n')

fig, axes = plt.subplots(1, 3, figsize=(13, 3.7), constrained_layout=True)
selected = [r for r in rows if r['C'] == 35]
n = [r['modes'] for r in selected]
for field, label, color in [('lowest_even', 'Even minimum', '#2166ac'),
                             ('lowest_odd', 'Odd minimum', '#b2182b')]:
    axes[0].plot(n, [abs(float(r[field])) for r in selected], 'o-', label=label, color=color)
axes[0].set_yscale('log')
axes[0].set(xlabel='Fourier rank N', ylabel='Absolute finite Ritz eigenvalue', title='C = 35: positive at N=32; negative thereafter')
axes[0].legend(fontsize=8)
axes[1].plot(n, [float(r['candidate_ground_overlap']) for r in selected], 'o-', color='#2166ac')
axes[1].set_yscale('symlog', linthresh=1e-13)
axes[1].set(xlabel='Fourier rank N', ylabel='Absolute unit-vector overlap', title='Prolate trial loses the finite ground')
r = records[35, 128]
reference = [float(x['line_zero']) for x in r['line_zero_offsets'] if float(x['line_zero']) <= 20]
roots = [float(x) for x in r['real_transform_roots'] if float(x) <= 20]
axes[2].eventplot([reference, roots], lineoffsets=[1, 0], linelengths=.5,
                  colors=['#2166ac', '#b2182b'])
axes[2].set(xlim=(0, 20), ylim=(-.7, 1.7), yticks=[0, 1],
            yticklabels=['Ground transform', 'DH line zeros'], xlabel='Height t',
            title='C = 35, N = 128: extra low roots')
for ax in axes:
    ax.grid(alpha=.2)
fig.suptitle('Finite DH diagnostics; no full-operator or RH conclusion', fontsize=13)
fig.savefig(ROOT/'finite_dh_spectral.png', dpi=170)
fig.savefig(ROOT/'finite_dh_spectral.svg')
plt.close(fig)
print('Wrote summary.json and finite_dh_spectral.png/.svg')
