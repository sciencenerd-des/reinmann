"""Plot only certified shift-44 signs and a labelled asymptotic diagnostic."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from flint import arb,ctx
from threshold_ground_gap import box

OUT=Path('research/prime_spectral/verification_2026_10_15_split_pair')


def run():
    extended=OUT/'column44_rank521-1400_32768bits.json'
    path=extended if extended.is_file() else OUT/'column44_rank521-677_32768bits.json'
    d=json.loads(path.read_text());a=json.loads((OUT/'split_pair_asymptotic.json').read_text())
    with ctx.workprec(256):
        angle=float(box(a['angle']).mid());phase=float(box(a['leading_constant_argument']).mid())
    r=np.arange(430,1401)
    fig,(top,bottom)=plt.subplots(2,1,figsize=(8.1,3.9),sharex=True,height_ratios=[2,1],layout='constrained')
    top.plot(r,np.cos(angle*r+phase),color='#246486',lw=1.6,label='Leading cosine: asymptotic diagnostic')
    top.axhline(0,color='.65',lw=.65);top.set_ylabel('Leading cosine')
    top.legend(loc='upper right',frameon=False,fontsize=9)
    top.set_ylim(-1.17,1.17)
    ranks=np.array([x['rank'] for x in d['per_rank']]);signs=np.array([1 if x['sign']=='positive' else -1 if x['sign']=='negative' else 0 for x in d['per_rank']])
    if np.any(signs==0):raise ValueError('unresolved data cannot be plotted as a sign')
    bottom.plot(np.arange(430,521),np.ones(91),color='.6',lw=3,label='Historical grid')
    for value,color in [(1,'#26755b'),(-1,'#b43c47')]:
        take=signs==value;bottom.scatter(ranks[take],signs[take],s=5,color=color,rasterized=False)
    bottom.axvline(663.5,color='.4',ls=':',lw=1)
    bottom.annotate('First negative rank: 664',xy=(664,-1),xytext=(750,-.35),fontsize=9,arrowprops={'arrowstyle':'->','color':'.4'})
    bottom.set_yticks([-1,1],['Negative','Positive']);bottom.set_ylabel('Certified sign')
    bottom.set_ylim(-1.4,1.4);bottom.set_xlabel('Rank r, fixed shift s = 44');bottom.set_xlim(430,1400)
    for ax in [top,bottom]:
        ax.spines[['top','right']].set_visible(False);ax.tick_params(labelsize=9)
    dest=Path('paper/figures');dest.mkdir(exist_ok=True)
    for ext in ['pdf','png']:fig.savefig(dest/f'dh_split_pair_column.{ext}',dpi=200)
    plt.close(fig)
    print('plotted',len(ranks),'certified signs; asymptotic line is not a finite-rank bound')


if __name__=='__main__':run()
