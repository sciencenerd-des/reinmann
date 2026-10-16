"""Only the requested DH shift-44 column, via complementary small minors.

Condensation in the *small determinant size* is workspace, not a new grid
survey. Selected 44 by 44 determinants independently check its signs.
"""
import argparse
import json
from pathlib import Path
import time
from flint import arb, arb_mat, arb_series, ctx
from full_ground_fourier import sha256
from threshold_ground_gap import box

OUT = Path('research/prime_spectral/verification_2026_10_15_split_pair')
OLD = Path('research/prime_spectral/verification_2026_10_12_sector')


def reciprocal(mu):
    old = ctx.cap
    try:
        ctx.cap = len(mu)
        f = arb_series([(-1)**j*x*arb(100)**j for j, x in enumerate(mu)])
        h = 1/f
        return [h[j] for j in range(len(mu))]
    finally:
        ctx.cap = old


def small_det(h, rank, shift=44):
    return arb_mat([[h[rank+i-j] if rank+i-j >= 0 else arb(0)
                     for j in range(shift)] for i in range(shift)]).det()


def column(h, shift=44):
    older, previous = [arb(1)]*len(h), list(h)
    for size in range(2, shift+1):
        current = [arb(1)]
        for r in range(1, len(h)-size+1):
            if older[r] is None or older[r].contains(0) or any(previous[j] is None for j in [r-1,r,r+1]):
                current.append(None)
            else:
                current.append((previous[r]**2-previous[r-1]*previous[r+1])/older[r])
        older, previous = previous, current
        if size % 8 == 0:
            print('small determinant size',size,'unresolved',sum(v is None or v.contains(0) for v in current),flush=True)
    return previous


def run(path, bits, min_rank, max_rank):
    start = time.monotonic()
    data = json.loads(path.read_text())
    with ctx.workprec(bits):
        mu = [box(x) for x in data['coefficients']]
        mu[0] = arb(1)
        max_rank = min(max_rank, len(mu)-44)
        if max_rank < min_rank:
            raise ValueError('insufficient coefficient coverage')
        h = reciprocal(mu)
        values = column(h)
        rows = []
        for r in range(min_rank,max_rank+1):
            d = values[r]
            sign = 'positive' if d is not None and d > 0 else 'negative' if d is not None and d < 0 else 'unresolved'
            rows.append({'rank':r,'sign':sign,'determinant_ball':d.str(60) if d is not None else None})
        negative = [r['rank'] for r in rows if r['sign']=='negative']
        checks = sorted(set([min_rank,max_rank,520]+
                            ([negative[0],negative[-1],negative[0]-1] if negative else [])))
        checked = []
        for r in checks:
            if not 1 <= r <= max_rank:
                continue
            d = small_det(h,r)
            if values[r] is None or not d.overlaps(values[r]) or d.contains(0):
                raise ArithmeticError(f'direct determinant unresolved or disagrees at {r}')
            checked.append({'rank':r,'determinant_ball':d.str(60)})
            print('direct rank',r,'sign',-1 if d<0 else 1,flush=True)
        result = {'status':'targeted_shift44_column','shift':44,'bits':bits,
                  'min_rank':min_rank,'max_rank':max_rank,
                  'negative_ranks':negative,'per_rank':rows,'direct_checks':checked,
                  'coefficient_file':str(path),'coefficient_sha256':sha256(path),
                  'source_sha256':{'dh_split_pair_column.py':sha256(Path(__file__))},
                  'seconds':time.monotonic()-start,
                  'positive_rescaling':'mu_n -> 100^n mu_n; determinant multiplied by 100^(rank*shift)',
                  'scope':'Only this solid-minor column. First in this interval is not globally first among all Toeplitz minors.'}
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/f'column44_rank{min_rank}-{max_rank}_{bits}bits.json').write_text(json.dumps(result,indent=2)+'\n')
    print('negative ranks',negative[:3],negative[-3:],'seconds',time.monotonic()-start,flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--coefficients',type=Path,default=OLD/'dh_rank430-520_shift0-200_32768bits_coefficients.json')
    p.add_argument('--bits',type=int,default=32768)
    p.add_argument('--min-rank',type=int,default=521)
    p.add_argument('--max-rank',type=int,default=1400)
    a=p.parse_args()
    run(a.coefficients,a.bits,a.min_rank,a.max_rank)
