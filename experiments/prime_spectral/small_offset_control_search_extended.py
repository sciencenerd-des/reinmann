"""Bounded selector over new primitive odd character labels; not an atlas."""
import json
from pathlib import Path
from flint import acb, arb, ctx, dirichlet_char
from character_zero_atlas import CharacterControl,center
from full_ground_fourier import sha256
from threshold_ground_gap import box

OUT=Path('research/prime_spectral/verification_2026_10_15_split_pair')


def run():
    observations=[]
    for q in [11,13,17,47,53,59,61,67,71,73]:
        for label in range(2,q):
            if label>=pow(label,-1,q):
                continue
            chi=dirichlet_char(q,label)
            if chi.parity()!=1 or not chi.is_primitive():
                continue
            control=CharacterControl(q,label)
            try:
                with ctx.workprec(256):
                    strip=control.strip()
            except ArithmeticError:
                continue
            roots=[]
            with ctx.workprec(112):
                for real in ['7/10','11/10']:
                    for j in range(3,121):
                        s=acb(real,j)
                        for _ in range(16):
                            f=control.jet(s,1)
                            if not f[1].is_finite() or f[1].contains(0):
                                break
                            w=s-f[0]/f[1]
                            if not w.is_finite() or not -1<s.real<3 or not 0<w.imag<130:
                                break
                            change=abs(w-s);s=acb(w.real.mid(),w.imag.mid())
                            if change<arb('1e-22'):
                                if (s.real>arb('500001/1000000') and
                                        not any(abs(s-center(r))<arb('1e-7') for r in roots)):
                                    roots.append(control.disk(s))
                                break
            roots.sort(key=lambda r:float(box(r['imag']).mid()))
            result={'conductor':q,'label':label,'selector_height':120,'roots':roots,
                    'lowest_observed_offset':str(box(roots[0]['real'])-arb('1/2')) if roots else None}
            observations.append(result)
            print(q,label,'off pairs found',len(roots),'first',result['lowest_observed_offset'],flush=True)
            payload={'status':'bounded_Newton_selectors_only','observations':observations,
                     'source_sha256':{Path(__file__).name:sha256(Path(__file__))},
                     'scope':'Individual Rouche disks only. No lowest-zero assertion before a complete atlas.'}
            OUT.mkdir(parents=True,exist_ok=True)
            (OUT/'small_offset_search_extended.json').write_text(json.dumps(payload,indent=2)+'\n')
            if roots:
                with ctx.workprec(256):
                    b=box(roots[0]['real'])-arb('1/2')
                    if arb('1/50')<b<arb('1/20'):
                        (OUT/'small_offset_candidate.json').write_text(json.dumps(result,indent=2)+'\n')
                        print('candidate requiring complete atlas',q,label,flush=True)
                        return
    print('no candidate with lowest observed offset in [0.02,0.05]',flush=True)


if __name__=='__main__':
    run()
