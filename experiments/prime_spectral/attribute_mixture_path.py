"""Finite-atlas attribution along the collision path; no infinite-tail bound."""
import argparse
import json
from pathlib import Path
from flint import ctx
import refine_calibration_atlases as refinement
from near_line_mixture_path import OUT,MixtureControl
from control_zero_attribution import attribute
from full_ground_fourier import sha256


def run(key):
    folder=OUT/key;definition=folder/'definition.json';control=MixtureControl(json.loads(definition.read_text())['t'])
    old=refinement.OUT
    try:
        refinement.OUT=folder;refinement.refine('mixture_path',control,folder/'atlas_H160/atlas.json')
    finally:refinement.OUT=old
    atlas=folder/'mixture_path_refined_atlas.json';d=json.loads(atlas.read_text())
    d['input_sha256'][str(definition)]=sha256(definition);d['source_sha256'].update({n:sha256(Path(__file__).with_name(n)) for n in ['attribute_mixture_path.py','near_line_mixture_control.py']})
    atlas.write_text(json.dumps(d,indent=2)+'\n')
    summary=folder/'window_search.json';s=json.loads(summary.read_text());path=Path(next(r['file'] for r in s['records'] if r['C']==s['negative_certificate_C']))
    with ctx.workprec(4096):result=attribute(key,atlas,path)
    result['status']='finite_collision_path_attribution_no_infinite_tail_bound';result['source_sha256']={n:sha256(Path(__file__).with_name(n)) for n in ['attribute_mixture_path.py','control_zero_attribution.py','near_line_mixture_control.py']}
    (folder/'attribution.json').write_text(json.dumps(result,indent=2)+'\n');print(key,'finite attribution complete',flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--key',choices=['b015','b008','b004'],required=True);run(p.parse_args().key)
