"""Check the generated band sources and optionally audit their actual Lean closure."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

from verify_xi_rectangle import strip_comments

ROOT = Path(__file__).resolve().parents[2]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def verify(rank, live, output):
    library = f'XiBand{rank}'
    plan = ROOT / f'research/prime_spectral/verification_2026_10_21_finite_bands/pf{rank}_plan.json'
    data = json.loads(plan.read_text())
    assert data['rank'] == rank and data['M'] == 1000
    assert data['Gamma_error'] == '1/25000000000000' and data['zeta_error'] == '1/5000'
    assert data['quarter'] == (['7/8', '1', '141/10', '19'] if rank == 58 else
                               ['29/40', '1', '141/10', '32'])
    assert data['source_sha256'] == hashlib.sha256(
        (ROOT / 'experiments/prime_spectral/finite_band_cover.py').read_bytes()).hexdigest()
    modules = sorted((ROOT / library).glob('*.lean')) + [ROOT / (library+'.lean')]
    assert len(modules) == 7*data['tile_count']+4
    shared = [ROOT / 'Reinmann' / (n+'.lean') for n in
              ['FiniteBandBounds', 'FiniteBandModel', 'FiniteBandTileRules', 'FiniteBandGeometry']]
    for path in modules+shared:
        assert not re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom)\b',
                             strip_comments(path.read_text())), path
    subprocess.run(['python3', 'experiments/prime_spectral/generate_finite_band_certificates.py',
                    '--plan', str(plan), '--check'], cwd=ROOT, check=True, stdout=subprocess.PIPE)
    if not live:
        print(f'Checked {len(modules)} generated {library} source files; no proof claim from this check.')
        return
    output.mkdir(parents=True, exist_ok=True)
    source = f'''import {library}
import Reinmann.XiFinitePFCertified

example : Reinmann.FinitePF Reinmann.XiMomentCoeff {rank} := Reinmann.{library}.finitePF{rank}

open Lean in
run_cmd do
  let env ← getEnv
  let mut names : Array Name := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if m == `{library} || "{library}.".isPrefixOf m.toString then
      let d := env.header.moduleData[i]!
      for j in [:d.constNames.size] do
        if d.constants[j]!.isTheorem then
          names := names.push d.constNames[j]!
  for n in names.qsort Name.lt do
    let axioms ← collectAxioms n
    if axioms.isEmpty then
      logInfo m!"'{{n}}' does not depend on any axioms"
    else
      logInfo m!"'{{n}}' depends on axioms: {{axioms.qsort Name.lt |>.map MessageData.ofConstName |>.toList}}"
  logInfo m!"BAND_AUDIT_COUNT {{names.size}}"

#print axioms Reinmann.XiFinitePFCertified.finitePF58_of_low_height_width
#print axioms Reinmann.XiFinitePFCertified.finitePF58
'''
    # The local file exists solely for this live kernel check, not as a proof assumption.
    tmp_root = ROOT / 'tmp'
    tmp_root.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=tmp_root, prefix='finite_band_audit_') as tmp:
        path = Path(tmp) / 'Audit.lean'
        path.write_text(source)
        result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = result.stdout.decode()
    (output / 'Audit.lean').write_text(source)
    (output / 'audit.log').write_text(log)
    assert result.returncode == 0 and 'error:' not in log, log[-4000:]
    flat = re.sub(r'\n\s+', ' ', log)
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", flat)
    empty = re.findall(r"'([^']+)' does not depend on any axioms", flat)
    count = int(re.search(r'BAND_AUDIT_COUNT (\d+)', log).group(1))
    assert count > data['tile_count']*10
    assert len(found)+len(empty) == count+2
    assert len({n for n, _ in found} | set(empty)) == count+2
    for name, axioms in found:
        assert {a.strip() for a in axioms.split(',')} <= ALLOWED, (name, axioms)
    assert f'Reinmann.{library}.finitePF{rank}' in {n for n, _ in found}
    receipt = {'status': 'actual_finite_band_kernel_audit_succeeded', 'rank': rank,
               'tiles': data['tile_count'], 'theorem_declarations_audited': count+2,
               'standard_axioms_only': True, 'finitePF_unconditional': True,
               'RH_proved': False, 'proof_commit': subprocess.check_output(
                   ['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
               'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                  for p in modules+shared+[plan]},
               'audit_log_sha256': hashlib.sha256(result.stdout).hexdigest()}
    (output / 'result.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(f'AXIOM-CLEAN: {count+2} actual finite-band declarations; unconditional PF{rank}.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rank', type=int, choices=(58, 97), required=True)
    parser.add_argument('--live-audit', action='store_true')
    parser.add_argument('--output', type=Path, default=ROOT / 'tmp/finite-band-audit')
    args = parser.parse_args()
    verify(args.rank, args.live_audit, args.output)
