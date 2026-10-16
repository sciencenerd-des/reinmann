"""Higher-precision replay of the targeted column and both band boundaries."""
import json
from pathlib import Path
from flint import arb,ctx
from dh_split_pair_column import OUT,reciprocal,column,small_det
from full_ground_fourier import sha256
from threshold_ground_gap import box


def run():
    path=OUT/'column44_rank521-1400_32768bits.json';d=json.loads(path.read_text())
    coefficients=Path(d['coefficient_file']);mu_data=json.loads(coefficients.read_text())
    with ctx.workprec(33024):
        mu=[box(x) for x in mu_data['coefficients']];mu[0]=arb(1);h=reciprocal(mu);values=column(h)
        for row in d['per_rank']:
            actual=values[row['rank']]
            if actual is None or actual.contains(0) or not actual.overlaps(arb(row['determinant_ball'])):
                raise ArithmeticError('enclosure mismatch at '+str(row['rank']))
            if ('positive' if actual>0 else 'negative')!=row['sign']:raise ArithmeticError('sign changed')
        direct=[]
        for r in [520,521,663,664,677,1099,1100,1400]:
            a=small_det(h,r)
            if a.contains(0) or not a.overlaps(values[r]):raise ArithmeticError('direct check failed')
            direct.append({'rank':r,'sign':'positive' if a>0 else 'negative','determinant_ball':a.str(60)})
        result={'status':'extended_targeted_column_replayed','bits':33024,'ranks_checked':880,
                'negative_ranks':[row['rank'] for row in d['per_rank'] if row['sign']=='negative'],
                'direct_checks':direct,'input_sha256':{str(path):sha256(path),str(coefficients):sha256(coefficients)},
                'source_sha256':{n:sha256(Path(__file__).with_name(n)) for n in
                                 ['replay_dh_split_pair_extended.py','dh_split_pair_column.py']},
                'scope':'Same FLINT backend and fresh Dirichlet-L coefficient enclosures; higher-precision determinant replay, not a third special-function implementation.'}
    (OUT/'column44_extended_replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'],'880 signs;',len(result['negative_ranks']),'negative;',len(direct),'direct checks')


if __name__=='__main__':run()
