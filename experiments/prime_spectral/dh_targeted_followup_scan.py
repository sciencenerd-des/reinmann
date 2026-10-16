"""Pre-registered second band and the explicitly requested nine-shift strip."""
import argparse
import json
from pathlib import Path
from flint import arb,ctx
from dh_split_pair_column import reciprocal,column,small_det
from full_ground_fourier import sha256
from threshold_ground_gap import box

OUT=Path('research/prime_spectral/verification_2026_10_15_second_band')


def run(path,shifts,low,high,bits=33024):
    data=json.loads(path.read_text());all_rows=[];direct=[]
    with ctx.workprec(bits):
        mu=[box(x) for x in data['coefficients']];mu[0]=arb(1);h=reciprocal(mu)
        if high+max(shifts)>=len(h):raise ValueError('coefficient coverage insufficient')
        for shift in shifts:
            values=column(h,shift)
            rows=[]
            for rank in range(low,high+1):
                a=values[rank];sign='unresolved' if a is None or a.contains(0) else 'positive' if a>0 else 'negative'
                rows.append({'rank':rank,'shift':shift,'sign':sign,'determinant_ball':a.str(45) if a is not None else None})
            negatives=[r['rank'] for r in rows if r['sign']=='negative']
            boundaries=set([low,high])
            for a,b in zip(rows,rows[1:]):
                if a['sign']!=b['sign']:boundaries.update([a['rank'],b['rank']])
            for rank in sorted(boundaries):
                a=small_det(h,rank,shift)
                if values[rank] is None or not a.overlaps(values[rank]) or a.contains(0):
                    raise ArithmeticError(f'direct check failed at {rank},{shift}')
                direct.append({'rank':rank,'shift':shift,'sign':'positive' if a>0 else 'negative','determinant_ball':a.str(45)})
            print('shift',shift,'negative range',negatives[:2],negatives[-2:],'unresolved',sum(r['sign']=='unresolved' for r in rows),flush=True)
            all_rows.extend(rows)
        result={'status':'targeted_followup_column_signs','bits':bits,'shifts':shifts,'min_rank':low,'max_rank':high,
                'per_cell':all_rows,'direct_checks':direct,
                'input_sha256':{str(path):sha256(path),str(OUT/'preregistered_forecast.json'):sha256(OUT/'preregistered_forecast.json')},
                'source_sha256':{n:sha256(Path(__file__).with_name(n)) for n in ['dh_targeted_followup_scan.py','dh_split_pair_column.py']},
                'scope':'Only declared cells. No global first minor claim; tail-coefficient analytic dependencies are inherited from input.'}
    name=f'shifts{min(shifts)}-{max(shifts)}_ranks{low}-{high}_{bits}bits.json'
    (OUT/name).write_text(json.dumps(result,indent=2)+'\n')
    print('wrote',name,flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--coefficients',type=Path,required=True)
    p.add_argument('--shifts',type=int,nargs='+',required=True);p.add_argument('--low',type=int,required=True);p.add_argument('--high',type=int,required=True)
    p.add_argument('--bits',type=int,default=33024);a=p.parse_args();run(a.coefficients,a.shifts,a.low,a.high,a.bits)
