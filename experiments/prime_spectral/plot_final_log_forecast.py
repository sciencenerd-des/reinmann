"""Standalone figure for the final finite-family mechanism test."""
import json
from fractions import Fraction
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from final_log_mixture_path import OUT
from full_ground_fourier import sha256

def main():
    p=OUT/'forecast_assessment.json';q=OUT/'preregistered_forecast.json';a=json.loads(p.read_text());f=json.loads(q.read_text())
    fig,axes=plt.subplots(1,3,figsize=(12,3.8),layout='constrained')
    for key,label in [('b001_N192','b=0.001, N192'),('b002_N192','b=0.002, N192'),('b001_N128','b=0.001, N128')]:
        rows=f['matched_spectrum_fits'][key]['rows'];axes[0].semilogy(*zip(*rows),'o-',label=label)
    axes[0].set(xlabel='Multiplicative cutoff C',ylabel='Lowest finite eigenvalue',title='Matched odd-gamma mixtures');axes[0].legend(fontsize=7)
    rows=f['saved_derivative_fit']['rows'];x=np.array([r[0] for r in rows]);y=np.array([r[1] for r in rows]);axes[1].semilogy(x,y,'o',label='Six saved unit-L2 witnesses');axes[1].semilogy(x,np.exp(f['saved_derivative_fit']['intercept']-f['kappa_prime']*x),'--',label=f"OLS κ′={f['kappa_prime']:.3f}")
    axes[1].set(xlabel='Multiplicative cutoff C',ylabel='Squared transform derivative',title='Saved-witness derivative decay');axes[1].legend(fontsize=7)
    xs=[r['b'] for r in a['rows']];axes[2].errorbar(xs,[r['mechanism_C'] for r in a['rows']],yerr=.25,fmt='s--',capsize=4,label='Frozen forecast ±0.25')
    for key,mark,label in [('negative_C_N192','o','Certified negative trial, N192'),('negative_C_N256','x','Certified negative trial, N256')]:axes[2].plot(xs,[r[key] for r in a['rows']],mark+'-',label=label)
    axes[2].set(xlabel='Off-line offset b',ylabel='Multiplicative cutoff C',title='Final held-out tests; no refit',xscale='log');axes[2].invert_xaxis();axes[2].set_xticks(xs,labels=['0.0005','0.00025']);axes[2].legend(fontsize=7)
    for ax in axes:ax.grid(alpha=.2)
    dest=Path('paper/figures/dh_final_log_mechanism');fig.savefig(dest.with_suffix('.pdf'));fig.savefig(dest.with_suffix('.png'),dpi=180)
    d={'status':'final_forecast_plot_generated_from_bound_inputs','input_sha256':{str(t):sha256(t) for t in [p,q]},'source_sha256':{Path(__file__).name:sha256(Path(__file__))},'scope':'Finite spectra, saved-witness fits and negative-support upper bounds only. Connecting lines are visual guides.'}
    (OUT/'plot_validation.json').write_text(json.dumps(d,indent=2)+'\n')
if __name__=='__main__':main()
