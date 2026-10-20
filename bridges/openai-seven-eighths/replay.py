"""Build the exact seven-eighths contract in an existing pinned OpenAI checkout.

No proof receipt is issued until both the upstream build and this wrapper pass.
Dependency installation and its resource use belong to the external project.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

PIN = '1581d4cbdd69a0faf34b2089614fe2a814316a6a'
HERE = Path(__file__).resolve().parent


def run(argv, cwd, output):
    started = time.monotonic()
    with output.open('w') as f:
        result = subprocess.run(argv, cwd=cwd, stdout=f, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'{argv} exited {result.returncode}; see {output}')
    return dict(command=argv, elapsed_seconds=time.monotonic()-started,
                log_sha256=hashlib.sha256(output.read_bytes()).hexdigest())


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--upstream', required=True, type=Path, help='openai/math checkout root')
    p.add_argument('--output', required=True, type=Path, help='new receipt directory')
    args = p.parse_args()
    root = args.upstream.resolve()
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
    if head != PIN:
        raise RuntimeError(f'Expected upstream {PIN}; got {head}')
    lean = root/'lean'
    if (lean/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.34.1':
        raise RuntimeError('Unexpected upstream toolchain')
    # Tracked source edits would invalidate the advertised source pin. Patched
    # dependency checkouts live below .lake and are governed by upstream Lake.
    if subprocess.check_output(['git', 'diff', 'HEAD', '--', 'lean'], cwd=root):
        raise RuntimeError('Upstream tracked Lean sources are modified')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    records = [run(['lake', 'build', 'OAI.NumberTheory.DirichletL.Nonvanishing'],
                   lean, output/'upstream-build.log')]
    records.append(run(['lake', 'env', 'lean', str(HERE/'SevenEighths.lean')],
                       lean, output/'contract.log'))
    audit = (output/'contract.log').read_text()
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
    expected = {'OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re',
                'Reinmann.zetaZeroFreeRightOf_sevenEighths'}
    if {name for name, _ in rows} != expected or len(rows) != 2:
        raise RuntimeError('Expected both explicit theorem axiom audits')
    for name, axioms in rows:
        if set(axioms.replace(',', ' ').split()) - {'propext', 'Classical.choice', 'Quot.sound'}:
            raise RuntimeError(f'Nonstandard axiom for {name}: {axioms}')
    receipt = dict(status='external_toolchain_contract_built_and_standard_axiom_audited',
                   upstream_commit=head, commands=records,
                   wrapper_sha256=hashlib.sha256((HERE/'SevenEighths.lean').read_bytes()).hexdigest(),
                   scope='Exact mirrored contract on Lean 4.34.1; no binary import into Lean 4.30.')
    (output/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(receipt['status'])


if __name__ == '__main__':
    main()
