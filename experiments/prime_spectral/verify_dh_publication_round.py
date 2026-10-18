"""Bind the unreviewed publication without rewriting the prior proof closure."""
import argparse,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'research/prime_spectral/verification_2026_10_18_publication'
PREVIOUS=ROOT/'research/prime_spectral/verification_2026_10_18_jacobi/manifest.json'
MANIFEST=OUT/'manifest.json'
MUTABLE={'README.md','paper/dh_controls_paper.tex','paper/dh_controls_paper.pdf','paper/zenodo_dh_controls.json','paper/DH_CONTROLS_REPRODUCTION.md'}
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def run(record=False):
 previous=json.loads(PREVIOUS.read_text());bound={}
 for name,h in previous['artifacts_sha256'].items():
  p=ROOT/name
  if name in MUTABLE:assert sha(OUT/'historical_96d6023'/name)==h,name
  else:assert sha(p)==h,name
  bound[p]=sha(p)
 auth=json.loads((OUT/'authorization.json').read_text());assert auth['human_review_prerequisite_waived'] and not auth['human_review_completed']
 receipt=json.loads((OUT/'publication_receipt.json').read_text());pre=json.loads((OUT/'publication_preflight.json').read_text());pdf=json.loads((OUT/'pdf_validation.json').read_text());bundle=json.loads((OUT/'publication_update_bundle.json').read_text());fresh=json.loads((OUT/'fresh_base_verification.json').read_text());update=json.loads((OUT/'DH_PUBLICATION_UPDATE.json').read_text())
 assert receipt['status']=='publication_verified_on_public_record_without_authentication' and receipt['doi']=='10.5281/zenodo.23401370' and receipt['files']==76
 assert pre['status']=='ready_to_publish_unreviewed_complete_fresh_verification_passed' and receipt['preflight_sha256']==sha(OUT/'publication_preflight.json')
 assert receipt['public_pdf_sha256']==pdf['pdf_sha256']==bundle['pdf_sha256']==sha(ROOT/'paper/dh_controls_paper.pdf')
 assert pdf['source_sha256']==sha(ROOT/'paper/dh_controls_paper.tex') and pdf['pages']==19
 assert fresh['members']==1005 and len(fresh['parts'])==70 and receipt['complete_supplement_verified']
 assert pre['publication_update_archive_sha256']==bundle['sha256']
 for name,item in update['publication_only_replacements'].items():
  assert sha(ROOT/name)==item['new_sha256'] and sha(ROOT/item['historical_path'])==item['old_sha256'],name
 assert json.loads((OUT/'monitor_stopped.json').read_text())['status']=='deleted'
 for p in OUT.rglob('*'):
  if p.is_file() and p!=MANIFEST:bound[p]=sha(p)
 for name in ['research/prime_spectral/DH_CONTROLS_PUBLICATION_2026_10_18.md','experiments/prime_spectral/verify_dh_publication_round.py','experiments/prime_spectral/verify_dh_publication_update.py','research/prime_spectral/verification_2026_10_18_draft_repair/manifest.json']:
  p=ROOT/name;bound[p]=sha(p)
 bound[PREVIOUS]=sha(PREVIOUS)
 result={'status':'unreviewed_publication_and_unchanged_scientific_proof_closure_verified','doi':receipt['doi'],'record_url':receipt['record_url'],'publication_date':'2026-10-18','publication_files':76,'prior_Lean_source_unchanged':True,'author_waiver_recorded':True,'human_review_completed':False,'updated_documents':sorted(MUTABLE),'scope':'Published unreviewed calibration preprint. No new mathematical theorem, numerical search, entire-function extension, Xi rectangle certificate or RH proof.','artifacts_sha256':{str(p.relative_to(ROOT)):h for p,h in sorted(bound.items())}}
 if record:
  if MANIFEST.exists():raise FileExistsError('Manifest exists; inspect differences before changing it')
  MANIFEST.write_text(json.dumps(result,indent=2)+'\n')
 else:assert json.loads(MANIFEST.read_text())==result,'Publication differs from manifest'
 print(result['status'],len(bound),'bound artifacts; DOI',receipt['doi'])
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');run(p.parse_args().record)
