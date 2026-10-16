"""Publication figures for the recorded band test and measured collision path."""
from fractions import Fraction
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from flint import ctx
from threshold_ground_gap import box

OUT=Path('research/prime_spectral/verification_2026_10_15_second_band');OLD=Path('research/prime_spectral/verification_2026_10_15_split_pair')


def save(fig,name):
    for ext in ['pdf','png']:fig.savefig(Path('paper/figures')/(name+'.'+ext),dpi=200)
    plt.close(fig)


def run():
    old=json.loads((OLD/'column44_rank521-1400_32768bits.json').read_text());new=json.loads((OUT/'shifts44-44_ranks1401-2000_33024bits.json').read_text());a=json.loads((OLD/'split_pair_asymptotic.json').read_text())
    with ctx.workprec(256):phi=float(box(a['angle']).mid());phase=float(box(a['leading_constant_argument']).mid())
    cells=old['per_rank']+new['per_cell'];r=np.arange(430,2001)
    fig,(top,bottom)=plt.subplots(2,1,figsize=(8.1,3.9),sharex=True,height_ratios=[2,1],layout='constrained')
    top.plot(r,np.cos(phi*r+phase),lw=1.5,color='#246486',label='Previously fixed leading cosine');top.axhline(0,color='.7',lw=.6);top.set_ylabel('Leading cosine');top.legend(frameon=False,fontsize=9,loc='upper right');top.set_ylim(-1.15,1.15)
    bottom.plot(np.arange(430,521),np.ones(91),color='.65',lw=3)
    for sign,y,color in [('positive',1,'#26755b'),('negative',-1,'#b43c47')]:
        ranks=[x['rank'] for x in cells if x['sign']==sign];bottom.scatter(ranks,np.full(len(ranks),y),s=4,color=color)
    for x in [1535,1539,1970,1974]:bottom.axvline(x,color='.5',ls=':',lw=.65)
    bottom.text(880,-.55,'664–1099',ha='center',fontsize=9);bottom.text(1754,-.55,'1536–1972',ha='center',fontsize=9)
    bottom.set_yticks([-1,1],['Negative','Positive']);bottom.set_ylim(-1.4,1.4);bottom.set_ylabel('Certified sign');bottom.set_xlabel('Rank r, fixed shift s = 44');bottom.set_xlim(430,2000)
    for ax in [top,bottom]:ax.spines[['top','right']].set_visible(False);ax.tick_params(labelsize=9)
    save(fig,'dh_second_band_column')
    d=json.loads((OUT/'collision_path_dataset.json').read_text());rows=d['rows']
    with ctx.workprec(256):
        b=np.array([float(box(x['b']).mid()) for x in rows]);gamma=np.array([float(box(x['gamma']).mid()) for x in rows]);r192=np.array([float(box(x['r_N192']).mid()) for x in rows]);C256=np.array([float(Fraction(x['C_N256'])) for x in rows]);r256=2*np.pi*C256/(13*gamma)
    fig,ax=plt.subplots(figsize=(7,3.9),layout='constrained');ax.plot(b,r192,'o-',color='#246486',label='N=192 negative-support upper bounds');ax.plot(b,r256,'^--',color='#c47c27',label='N=256 negative-support upper bounds')
    for x,y,row in zip(b,r192,rows):ax.annotate(f'C={float(Fraction(row["C_N192"])):.4g}',(x,y),xytext=(0,9),textcoords='offset points',ha='center',fontsize=9)
    ax.set_xscale('log');ax.invert_xaxis();ax.set_xticks(b,[f'{x:g}' for x in b]);ax.set_xlabel('Off-line offset b (decreasing to the right)');ax.set_ylabel('r = 2πC / (13γ)');ax.legend(frameon=False,fontsize=9,loc='lower right');ax.grid(alpha=.15);ax.set_ylim(min(r256)-.015,max(r192)+.025);ax.spines[['top','right']].set_visible(False)
    save(fig,'dh_mixture_collision_path');print('Two finite-certificate figures written; connecting lines are guides only',flush=True)


if __name__=='__main__':run()
