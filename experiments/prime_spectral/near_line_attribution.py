"""Refine the mixture atlas and attribute its certified negative witness."""
import json
from pathlib import Path
from flint import ctx
import refine_calibration_atlases as refinement
from near_line_mixture_control import OUT,MixtureControl
from control_zero_attribution import attribute
from full_ground_fourier import sha256


def run():
    definition=OUT/'near_line_mixture_definition.json'
    control=MixtureControl(json.loads(definition.read_text())['t'])
    old=refinement.OUT
    try:
        refinement.OUT=OUT
        refinement.refine('nearline_mixture',control,OUT/'mixture13_H160/atlas.json')
    finally:
        refinement.OUT=old
    atlas=OUT/'nearline_mixture_refined_atlas.json'
    data=json.loads(atlas.read_text())
    data['input_sha256'][str(definition)]=sha256(definition)
    data['source_sha256']['near_line_mixture_control.py']=sha256(Path(__file__).with_name('near_line_mixture_control.py'))
    data['source_sha256']['near_line_attribution.py']=sha256(Path(__file__))
    atlas.write_text(json.dumps(data,indent=2)+'\n')
    summary=OUT/'mixture13_windows/search_N192_2048bits.json'
    search=json.loads(summary.read_text());high=search['negative_certificate_C']
    trial=Path(next(r['file'] for r in search['records'] if r['C']==high))
    with ctx.workprec(2048):
        result=attribute('nearline_mixture',atlas,trial)
    result['status']='finite_mixture_atlas_attribution_no_infinite_tail_bound'
    result['source_sha256']={n:sha256(Path(__file__).with_name(n)) for n in
                            ['near_line_attribution.py','control_zero_attribution.py',
                             'near_line_mixture_control.py','refine_calibration_atlases.py']}
    (OUT/'nearline_attribution.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    run()
