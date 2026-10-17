"""Standalone scientific figure from frozen forecasts and checked endpoints."""
from pathlib import Path
import json
from fractions import Fraction
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from plain_l13_decay import OUT
from full_ground_fourier import sha256


def mid(e):return float((Fraction(e['lo'])+Fraction(e['hi']))/2)


def run():
    p=OUT/'forecast_assessment.json';d=json.loads(p.read_text());inputs={str(p):sha256(p)}
    fig,axes=plt.subplots(1,2,figsize=(10,4),layout='constrained')
    for N,marker in [(96,'o'),(128,'s')]:
        xs=[16,20,24,28,32];ys=[]
        for C in xs:
            p0=OUT/f'plain_quadratic_L13_C{C}_N{N}_768bits.json';e=json.loads(p0.read_text());ys.append(mid(e['sectors'][0]['lowest_eigenvalues'][0]));inputs[str(p0)]=sha256(p0)
        axes[0].semilogy(xs,ys,marker+'-',label=f'N={N}')
    axes[0].set(xlabel='Multiplicative window C',ylabel='Lowest finite eigenvalue',title='Plain quadratic L13: registered fit range')
    axes[0].text(.04,.06,f"κ fit at N128 = {d['kappa13_primary']:.6f}",transform=axes[0].transAxes)
    axes[0].legend();axes[0].grid(alpha=.2)
    b=[r['b'] for r in d['rows']]
    for key,marker,label in [('mechanism','s','Frozen plain-L κ forecast'),('descriptive','^','Frozen descriptive forecast')]:
        axes[1].plot(b,[r['prediction'][key+'_C'] for r in d['rows']],marker+'--',label=label)
    axes[1].plot(b,[r['C_N192'] for r in d['rows']],'o-',color='black',label='N192 negative-support upper bound')
    axes[1].plot(b,[r['C_N256'] for r in d['rows']],'x',color='gray',label='N256 negative-support upper bound')
    axes[1].set(xlabel='Off-line offset b',ylabel='Multiplicative window C',title='Held-out targets; no forecast refit')
    axes[1].set_xscale('log');axes[1].invert_xaxis();axes[1].set_xticks(b,labels=['0.002','0.001']);axes[1].grid(alpha=.2);axes[1].legend(fontsize=7)
    dest=Path('paper/figures/dh_log_forecast');dest.parent.mkdir(exist_ok=True)
    fig.savefig(dest.with_suffix('.pdf'));fig.savefig(dest.with_suffix('.png'),dpi=180)
    (OUT/'plot_validation.json').write_text(json.dumps({'status':'forecast_plot_generated_from_bound_inputs','input_sha256':inputs,'source_sha256':{Path(__file__).name:sha256(Path(__file__))},'scope':'Finite eigenvalues and negative-support upper bounds. Connecting lines are guides; no fitted universal law or full-support bracket.'},indent=2)+'\n')


if __name__=='__main__':run()
