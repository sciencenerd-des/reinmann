"""Compare the pre-recorded DH band forecast with resolved new intervals."""
import json
from pathlib import Path
from flint import ctx
from threshold_ground_gap import box
from full_ground_fourier import sha256

OUT=Path('research/prime_spectral/verification_2026_10_15_second_band')


def run():
    f=OUT/'preregistered_forecast.json';p=OUT/'shifts44-44_ranks1401-2000_33024bits.json'
    n=OUT/'shifts40-48_ranks521-700_33024bits.json'
    old=Path('research/prime_spectral/verification_2026_10_15_split_pair/split_pair_asymptotic.json')
    forecast=json.loads(f.read_text());data=json.loads(p.read_text());near=json.loads(n.read_text());a=json.loads(old.read_text())
    if any(x['sign']=='unresolved' for x in data['per_cell']+near['per_cell']):raise ValueError('unresolved cells')
    negative=[x['rank'] for x in data['per_cell'] if x['sign']=='negative']
    if negative!=list(range(min(negative),max(negative)+1)):raise ValueError('band is not contiguous')
    observed=[min(negative),max(negative)];spec=forecast['second_band_forecast']
    passes=[lo<=x<=hi for x,(lo,hi) in zip(observed,[spec['negative_entry_rank_interval'],spec['last_negative_rank_interval']])]
    with ctx.workprec(512):
        phi=box(a['angle']);phase=box(a['leading_constant_argument']);matches=[]
        for row in data['per_cell']:
            cosine=(phi*row['rank']+phase).cos()
            if cosine.contains(0):raise ArithmeticError('leading diagnostic sign unresolved')
            matches.append(('positive' if cosine>0 else 'negative')==row['sign'])
    first=min((x['rank'],x['shift']) for x in near['per_cell'] if x['sign']=='negative')
    result={'status':'preregistered_second_band_forecast_tested','observed_band':observed,'forecast_passes':passes,
            'nominal_errors':[x-y for x,y in zip(observed,spec['nominal_band'])],
            'leading_cosine_signs_matching':sum(matches),'leading_cosine_signs_compared':len(matches),
            'entry_displacement_from_first_band':observed[0]-664,'last_negative_displacement_from_first_band':observed[1]-1099,
            'nearby_cells':len(near['per_cell']),'first_negative_nearby_cell':{'rank':first[0],'shift':first[1]},
            'input_sha256':{str(x):sha256(x) for x in [f,p,n,old]},
            'source_sha256':{Path(__file__).name:sha256(Path(__file__))},
            'scope':'Locally preregistered forecast, not independently public timestamped. Confirms these finite band predictions, not an all-rank quantitative remainder theorem or globally first failing minor.'}
    (OUT/'forecast_assessment.json').write_text(json.dumps(result,indent=2)+'\n');print(observed,passes,'cosine matches',sum(matches),'/',len(matches),flush=True)


if __name__=='__main__':run()
