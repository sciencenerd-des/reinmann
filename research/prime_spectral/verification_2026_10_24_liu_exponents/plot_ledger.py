"""Plot the checked scalar ledger; figures are not analytic estimates."""
from fractions import Fraction as F
import json
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
r = json.loads((ROOT/'scalar_verified.json').read_text())
fig, axes = plt.subplots(1, 2, figsize=(10.8, 4), constrained_layout=True)
ell = [F(1, 10)+F(i, 1000) for i in range(201)]
naive = [F(11, 12)-v/4 for v in ell]
full = [v+max(F(0), 5*u-1)/8 for v, u in zip(naive, ell)]
axes[0].plot(list(map(float, ell)), list(map(float, full)), color='#2166ac', label='Full direct majorant (balanced)')
axes[0].plot(list(map(float, ell)), list(map(float, naive)), '--', color='#999999', label='Truncated identity')
axes[0].axhline(13/15, color='#b2182b', linestyle=':', label='Exact direct LP floor 13/15')
axes[0].set(xlabel='Auxiliary prime-length exponent ell', ylabel='Required boundary B',
            title='The omitted reflection term stops the descent')
axes[0].legend(fontsize=8)
lo, hi = map(F, r['regression_values']['variable_moment_B_interval'])
fixed = (lo+hi)/2
values = [F(7, 8)]+[sum(map(F, d['new_B_interval']))/2
                       for d in r['bootstrap_intervals_from_preceding_bound']]
axes[1].semilogy(range(len(values)), [float(v-fixed) for v in values], 'o-', color='#2166ac')
axes[1].set(xlabel='Bootstrap step (0 = 7/8)', ylabel='B at step minus limiting B',
            title='Exact interval replay approaches Liu v2')
for ax in axes:
    ax.grid(alpha=.2)
fig.suptitle('Scalar reconstruction; no new Hecke-family or RH estimate', fontsize=12)
fig.savefig(ROOT/'liu_exponent_ledger.png', dpi=170)
fig.savefig(ROOT/'liu_exponent_ledger.svg')
plt.close(fig)
print('Wrote liu_exponent_ledger.png/.svg')
