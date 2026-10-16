"""Reproduce the added figures from certified records and check caption numbers.

Positions/bars use ball midpoints for display. Assertions use whole outward
balls, including root disk radii. Written analytic dependencies are unchanged.
"""
import argparse
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from flint import arb,ctx
from threshold_ground_gap import box
from full_ground_fourier import sha256
from certified_weil import endpoints

OUT=Path('research/prime_spectral/verification_2026_10_16_figures')
ATLAS=Path('research/prime_spectral/verification_2026_10_13_calibration/dh5_refined_atlas.json')
ATTR=Path('research/prime_spectral/verification_2026_10_13_calibration/zero_attribution.json')
NAMES={'dh5':'DH5','q13_label2':'DH13(2)','epstein5':'Epstein5','q17_label3':'DH17(3)','q7_label3':'DH7(3)','q13_label6':'DH13(6)','epstein6':'Epstein6'}


def root(record):
    r=arb(record['radius']);b=box(record['real'])-arb('1/2')+arb(0,r)
    gamma=box(record['imag'])+arb(0,r)
    return b,gamma


def save(fig,folder,name):
    fig.savefig(folder/(name+'.pdf'),bbox_inches='tight');fig.savefig(folder/(name+'.png'),dpi=180,bbox_inches='tight');plt.close(fig)


def run(folder):
    folder.mkdir(parents=True,exist_ok=True)
    with ctx.workprec(768):
        a=json.loads(ATLAS.read_text());d=json.loads(ATTR.read_text())
        line=[root(r)[1]**2 for r in a['critical_line_disks']]
        off=[]
        for record in a['right_off_line_zeros']:
            b,g=root(record);assert b>0 and g>0
            off.append((b*b+g*g,2*(b/g).atan(),b,g))
        steep=max(range(len(off)),key=lambda j:float(off[j][1].mid()));mod,phi,b,g=off[steep]
        assert all(off[j][1]<phi for j in range(len(off)) if j!=steep)
        assert arb.pi()/437<phi<arb.pi()/436
        assert sum(x<mod for x in line)==43 and all(x<mod or x>mod for x in line)
        assert sum(x<64 for x in line)==1 and all(x<64 or x>64 for x in line)
        assert all(x[0]>64 for x in off)
        tail=2*(arb(1)/340).atan();assert tail<phi
        results=[];labels=[];bars=[];ratios=[]
        for control in d['controls']:
            w=control['witnesses'][0];j=w['dominant_negative_quartet_index']
            q=box(w['geometric_full_quotient']);p=box(w['finite_total']);L=box(w['finite_line_sum']);D=box(w['off_line_quartets'][j]['quartet_contribution'])
            assert D<0 and q<0 and p<0 and L>0
            mismatch=100*abs(abs(D)-L)/L;ratio=abs(p/q)
            assert mismatch<16 and ratio>257 and ratio<12564
            results.append({'name':control['name'],'relative_mismatch_percent_to_line':endpoints(mismatch),'finite_total_over_quotient_magnitude':endpoints(ratio)})
            labels.append(NAMES[control['name']]);bars.append([float(abs(v).mid()) for v in [D,L,p,q]]);ratios.append(float(ratio.mid()))
        assert sum(box(r['relative_mismatch_percent_to_line'])<arb('3.5') for r in results)==5
        validation={'status':'added_figure_caption_numbers_verified','line_zero_count':len(line),'off_line_pair_count':len(off),'inner_line_zero_count':43,'single_folded_zero_inside_radius64':True,
                    'folded_zero_sign':'w=-gamma1^2; corresponding reciprocal pole is z=+gamma1^2 in 1/F(-z)',
                    'steepest_phi':endpoints(phi),'folded_pair_modulus':endpoints(mod),'high_zero_angle_envelope_at340':endpoints(tail),'attribution':results,
                    'input_sha256':{str(p):sha256(p) for p in [ATLAS,ATTR]},'source_sha256':{Path(__file__).name:sha256(Path(__file__))},
                    'scope':'Caption numbers and display coordinates checked against prior certified inputs; figures show midpoints, not additional zero certificates or an infinite-tail bound.'}
        xs=np.array([float(x.mid()) for x in line]);ox=np.array([float(x[0].mid()) for x in off]);oy=np.array([float(x[1].mid()) for x in off]);p435=float((arb.pi()/436).mid());p436=float((arb.pi()/437).mid())
    fig,ax=plt.subplots(figsize=(8,4.2));ax.set_xscale('log');ax.axvspan(10,340**2,color='#f0f4fa')
    ax.scatter(xs,np.zeros(len(xs)),marker='|',color='#265dab',s=60,label='235 critical-line zeros')
    ax.scatter(ox,oy,color='#b64d37',s=28,label='7 off-line pairs (upper folded member)',zorder=3)
    ax.axhline(p435,color='#2d8c58',lw=1,label='π/436: PF435 sufficient wedge');ax.axhline(p436,color='#2d8c58',ls=':',lw=.9,label='π/437: PF436 not guaranteed')
    ax.axvline(64,color='#c88c22',lw=1);ax.text(70,.011,'|w|=64',color='#c88c22',fontsize=9)
    ax.scatter([min(xs)],[0],marker='s',s=48,color='#c88c22',label='Folded zero w=-γ₁²; radius γ₁²',zorder=4)
    radius=np.geomspace(340**2+1,4e5,160);envelope=2*np.arctan(1/np.sqrt(radius-1))
    ax.plot(radius,envelope,'--',color='.4',label='Tail envelope from γ>340, |b|<1')
    ax.annotate('Steepest pair: ψ≈0.007200',(ox[steep],oy[steep]),xytext=(150,.0102),fontsize=9,arrowprops={'arrowstyle':'-','color':'.3'})
    ax.text(120,.0034,'43 preceding line zeros\nSplit shift s=44',color='#265dab',fontsize=9)
    inset=ax.inset_axes([.72,.55,.25,.38]);inset.axhline(p435,color='#2d8c58',lw=1);inset.axhline(p436,color='#2d8c58',ls=':',lw=1);inset.scatter([ox[steep]],[oy[steep]],color='#b64d37',s=25)
    inset.set_xlim(6500,8500);inset.set_ylim(.007175,.007225);inset.set_title('π/437 < ψ < π/436',fontsize=8);inset.tick_params(labelsize=7);inset.spines[['top','right']].set_visible(False)
    ax.set_xlim(10,4e5);ax.set_ylim(-.0006,.0125);ax.set_ylabel('Angular deviation ψ from the negative axis (rad)');ax.set_xlabel('Folded radius |w|, w=(ρ-1/2)² (log scale)');ax.set_title('Folded DH zeros, the sector wedge and split pair',fontsize=11)
    ax.grid(alpha=.15);ax.spines[['top','right']].set_visible(False);ax.legend(loc='upper center',bbox_to_anchor=(.5,-.22),ncol=2,fontsize=8,frameon=False);save(fig,folder,'dh_folded_wedge_verified')
    values=np.array(bars);x=np.arange(len(labels));width=.19
    fig,ax=plt.subplots(figsize=(9.2,3.6));colours=['#bd6a52','#4674b2','#cf9b3e','#333333'];names=['Dominant off-line quartet','Critical-line sum','Finite total P_H','Certified quotient Q'];signs=['-','+','-','-']
    for j in range(4):
        locations=x+(j-1.5)*width;ax.bar(locations,values[:,j],width=width,color=colours[j],label=names[j])
        for loc,value in zip(locations,values[:,j]):ax.text(loc,value*1.5,signs[j],ha='center',va='bottom',fontsize=9,color=colours[j])
    ax.set_yscale('log');ax.set_ylim(1e-45,1e7);ax.set_xticks(x,[label+'\n|P_H/Q|≈'+str(round(r)) for label,r in zip(labels,ratios)],fontsize=8);ax.set_ylabel('Magnitude (log scale); sign above bar');ax.set_title('Finite-atlas cancellation and the uncertified omitted tail',fontsize=11)
    ax.legend(loc='upper center',ncol=4,fontsize=7,frameon=False);ax.grid(axis='y',alpha=.2);ax.spines[['top','right']].set_visible(False);save(fig,folder,'dh_attribution_bars_verified')
    OUT.mkdir(exist_ok=True);(OUT/'figure_validation.json').write_text(json.dumps(validation,indent=2)+'\n')
    print('Caption assertions passed; two figures reproduced from bound inputs',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=Path('tmp/figure-replay-2026-10-16'));run(p.parse_args().output)
