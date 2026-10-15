"""Build descriptive seven-control fits and manuscript tables from checked records."""
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

OUT = Path('research/prime_spectral/verification_2026_10_13_calibration')
SPECS = [
    ('dh5', 'DH5', 'character5_label2_windows', 1, 5),
    ('q13_label2', 'DH13(2)', 'character13_label2_windows', 1, 13),
    ('epstein5', 'Epstein5', 'epstein5_label0_windows', 2, 5),
    ('q17_label3', 'DH17(3)', 'character17_label3_windows', 1, 17),
    ('q7_label3', 'DH7(3)', 'character7_label3_windows', 1, 7),
    ('q13_label6', 'DH13(6)', 'character13_label6_windows', 1, 13),
    ('epstein6', 'Epstein6', 'epstein6_label0_windows', 2, 6),
]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def middle(ball):
    return float((Fraction(ball['lo'])+Fraction(ball['hi']))/2)


def resolution(C, degree, parameter):
    return 2*math.pi*C/parameter if degree == 1 else math.pi*math.sqrt(C/parameter)


def fit(rows, degree_effect):
    y = np.array([r['resolution_ratio'] for r in rows])
    X = np.array([[1, r['offset_b'], r['gamma_degree']-1] if degree_effect else [1, r['offset_b']]
                  for r in rows])
    if np.linalg.matrix_rank(X) != X.shape[1]:
        raise ValueError('descriptive model is not identifiable even on this finite sample')
    coefficients = np.linalg.lstsq(X, y, rcond=None)[0]
    residual = X@coefficients-y
    loo = []
    for i in range(len(rows)):
        keep = np.arange(len(rows)) != i
        beta = np.linalg.lstsq(X[keep], y[keep], rcond=None)[0]
        prediction = float(X[i]@beta)
        actual = float(y[i])
        C_ratio = (prediction/actual)**rows[i]['gamma_degree']
        loo.append({'name': rows[i]['name'], 'predicted_r': prediction,
                    'observed_upper_bound_r': actual, 'C_relative_error_percent': 100*(C_ratio-1)})
    return {'model': 'r=a+k*b+d*(degree-1)' if degree_effect else 'r=a+k*b',
            'coefficients': coefficients.tolist(), 'r_RMSE': float(np.sqrt(np.mean(residual**2))),
            'leave_one_out': loo, 'sample_size': len(rows),
            'scope': 'Descriptive fit to finite-family negative-support upper bounds, not independent minimum-support measurements. No statistical confidence interval or universal theorem.'}


def scientific(value):
    if not value:
        return '0'
    exponent = math.floor(math.log10(abs(value)))
    mantissa = value/10**exponent
    return f'{mantissa:.3f}\\times10^{{{exponent}}}'


def run():
    rows, inputs = [], {}
    for name, label, folder, degree, parameter in SPECS:
        atlas_path = OUT/f'{name}_refined_atlas.json'
        search_path = OUT/folder/'search_N192_2048bits.json'
        atlas = json.loads(atlas_path.read_text())
        search = json.loads(search_path.read_text())
        if atlas['status'] != 'complete_parent_atlas_with_refined_disks' or search['status'] != 'finite_family_search_with_certified_negative_endpoint':
            raise ValueError('complete atlas and negative endpoint required')
        zero = atlas['right_off_line_zeros'][0]
        gamma, b = middle(zero['imag']), middle(zero['real'])-.5
        C = float(Fraction(search['negative_certificate_C']))
        rows.append({'name': name, 'label': label, 'gamma_degree': degree, 'parameter': parameter,
                     'lowest_off_line_height': gamma, 'offset_b': b, 'atlas_height': atlas['height'],
                     'positive_finite_evidence_C': search['positive_finite_evidence_C'],
                     'negative_certificate_C': search['negative_certificate_C'],
                     'negative_C_float': C, 'modes': 192, 'bits': 2048,
                     'resolution_height': resolution(C, degree, parameter),
                     'resolution_ratio': resolution(C, degree, parameter)/gamma})
        inputs.update({str(p): sha(p) for p in [atlas_path, search_path]})
    prediction_path = OUT/'q17_prediction.json'
    prediction = json.loads(prediction_path.read_text())
    q17 = next(r for r in rows if r['name'] == 'q17_label3')
    # This is the originally supplied forecast; later fits do not revise it.
    prediction.update(observed_negative_C=q17['negative_C_float'],
                      negative_endpoint_in_prediction_interval=prediction['prediction_interval_C'][0] <= q17['negative_C_float'] <= prediction['prediction_interval_C'][1],
                      negative_endpoint_error_percent=100*(q17['negative_C_float']/prediction['target_C']-1))
    # Linear interpolation uses only the original two bracketing offsets.
    original_C = {'dh5': 30.75390625, 'q13_label2': 33.875, 'epstein5': 19.875}
    training = []
    for r in rows[:3]:
        training.append({**r, 'resolution_ratio': resolution(original_C[r['name']], r['gamma_degree'], r['parameter'])/r['lowest_off_line_height']})
    bracketing = sorted([r for r in training if r['name'] in ['dh5', 'q13_label2']], key=lambda r: r['offset_b'])
    left, right = bracketing
    ratio = left['resolution_ratio']+(q17['offset_b']-left['offset_b'])*(right['resolution_ratio']-left['resolution_ratio'])/(right['offset_b']-left['offset_b'])
    prediction['original_bracketing_linear_interpolation_C'] = ratio*q17['lowest_off_line_height']*17/(2*math.pi)
    prediction['scope'] = 'A certified negative endpoint lies in the forecast band. Positive finite evidence does not certify the minimum full onset or an exclusion law.'
    simple, degree_fit = fit(rows, False), fit(rows, True)
    attribution_path = OUT/'zero_attribution.json'
    attribution = json.loads(attribution_path.read_text())
    inputs.update({str(p): sha(p) for p in [prediction_path, attribution_path]})
    result = {'status': 'descriptive_seven_control_calibration_from_certified_negative_trials',
              'controls': rows, 'fits': [simple, degree_fit], 'q17_prediction_assessment': prediction,
              'input_sha256': inputs, 'source_sha256': {'build_control_calibration.py': sha(Path(__file__))},
              'scope': 'Seven finite-family negative upper bounds at common N=192, not seven minimum-window measurements. No universal Phi, small-offset asymptotic or zeta zero-exclusion claim.'}
    (OUT/'calibration_dataset.json').write_text(json.dumps(result, indent=2)+'\n')
    table = [r'\begin{table}[ht]', r'\centering', r'\small',
             r'\caption{Common-degree calibration, $N=192$. $C_+$ means positive finite evidence; $C_-$ is a certified negative full-form trial. The values are rounded; exact rational endpoints are retained in the supplement. $r=T_*(C_-)/\gamma$.}\label{tab:calibration}',
             r'\begin{tabular}{lrrrrr}', r'\toprule Control & $\gamma$ & $b$ & $C_+$ & $C_-$ & $r$\\\midrule']
    for r in rows:
        low = float(Fraction(r['positive_finite_evidence_C']))
        table.append(f"{r['label']} & {r['lowest_off_line_height']:.6f} & {r['offset_b']:.6f} & {low:.6f} & {r['negative_C_float']:.6f} & {r['resolution_ratio']:.5f} "+r'\\')
    table += [r'\bottomrule', r'\end{tabular}', r'\end{table}']
    Path('paper/dh_controls_tables.tex').write_text('\n'.join(table)+'\n')
    table = [r'\begin{table}[ht]', r'\centering\small',
             r'\caption{Attribution for each common-degree negative endpoint witness. The dominant negative quartet is the lowest off-line pair in all seven finite atlases. $P_H$ is the sum over the complete atlas below height $H$; $Q$ is the certified geometric quotient. Their difference is material, so the finite sum is mechanism evidence rather than a negligible-tail spectral certificate.}\label{tab:attribution}',
             r'\begin{tabular}{lcrrr}', r'\toprule Control & Parity & Dominant $\gamma$ & $Q$ & $P_H$\\\midrule']
    for control in attribution['controls']:
        label = next(r['label'] for r in rows if r['name'] == control['name'])
        for w in control['witnesses']:
            dominant = w['dominant_negative_quartet_index']
            gamma = middle(w['off_line_quartets'][dominant]['gamma']) if dominant is not None else float('nan')
            table.append(f"{label} & {w['parity']} & {gamma:.6f} & $"+scientific(middle(w['geometric_full_quotient']))+'$ & $'+scientific(middle(w['finite_total']))+r'$\\')
    table += [r'\bottomrule', r'\end{tabular}', r'\end{table}']
    Path('paper/dh_controls_attribution_table.tex').write_text('\n'.join(table)+'\n')
    fig, ax = plt.subplots(figsize=(7.7, 4.8), layout='constrained')
    for degree, marker, color, text in [(1, 'o', '#1e5e91', 'Character completions, degree 1'),
                                       (2, 's', '#c16b25', 'Epstein completions, degree 2')]:
        selected = [r for r in rows if r['gamma_degree'] == degree]
        ax.scatter([r['offset_b'] for r in selected], [r['resolution_ratio'] for r in selected],
                   marker=marker, color=color, s=65, label=text, zorder=4)
        for r in selected:
            dx, ha = (-5, 'right') if r['name'] == 'q7_label3' else (5, 'left')
            ax.annotate(r['label'], (r['offset_b'], r['resolution_ratio']),
                        xytext=(dx, 6 if r['name'] != 'epstein6' else -15),
                        textcoords='offset points', fontsize=9, ha=ha)
    xs = np.linspace(min(r['offset_b'] for r in rows), max(r['offset_b'] for r in rows), 200)
    a, k = simple['coefficients']
    ax.plot(xs, a+k*xs, color='#777777', ls='--', lw=1.5, label='Descriptive linear fit')
    a, k, d = degree_fit['coefficients']
    ax.plot(xs, a+k*xs, color='#1e5e91', lw=1, alpha=.65)
    ax.plot(xs, a+k*xs+d, color='#c16b25', lw=1, alpha=.65, label='Descriptive degree-effect fits')
    forecast_r = [resolution(c, 1, 17)/q17['lowest_off_line_height'] for c in [126, 140, 154]]
    ax.errorbar(q17['offset_b'], forecast_r[1], yerr=[[forecast_r[1]-forecast_r[0]], [forecast_r[2]-forecast_r[1]]],
                fmt='none', color='#3e8951', capsize=4, lw=1.8, label='Recorded q17 C=140 ±10% forecast')
    ax.set(xlabel='Lowest off-line offset b', ylabel='r = normalized resolution / zero height',
           title='Seven negative-window upper bounds at common trial degree 192')
    ax.grid(alpha=.18)
    ax.legend(fontsize=8, loc='lower left')
    folder = Path('paper/figures');folder.mkdir(exist_ok=True)
    for suffix in ['pdf', 'png']:
        fig.savefig(folder/f'dh_controls_calibration.{suffix}', dpi=180, bbox_inches='tight')
    plt.close(fig)
    for r in rows:
        print(r['label'], f"b={r['offset_b']:.6f}", f"C-={r['negative_C_float']:.8f}", f"r={r['resolution_ratio']:.6f}")
    print('q17 recorded prediction error percent', prediction['negative_endpoint_error_percent'])
    print('fit RMSE', simple['r_RMSE'], degree_fit['r_RMSE'])


if __name__ == '__main__':
    run()
