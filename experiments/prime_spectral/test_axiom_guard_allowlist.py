"""Exercise the actual shell guard with controlled #print-axioms output.

Only the lake invocation is replaced. The real source scanner and dependency
parser run, so a subset regression or a forbidden-axiom bypass is detected.
This fixture test is separate from the real Lean audit.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
GUARD = ROOT / 'scripts/verify_axiom_clean.sh'
CASES = (
    ('three_standard', '[propext, Classical.choice, Quot.sound]', 0),
    ('proper_subset', '[propext, Quot.sound]', 0),
    ('wrapped_subset', '\n  [propext, Quot.sound]', 0),
    ('native_reduction', '[propext, Classical.choice, Quot.sound, Lean.ofReduceBool]', 1),
    ('sorry_axiom', '[propext, Classical.choice, Quot.sound, sorryAx]', 1),
    ('custom_axiom', '[propext, custom_axiom]', 1),
    ('malformed_output', 'unchecked', 1),
)


def run(output):
    output.mkdir(parents=True, exist_ok=True)
    rows = []
    with tempfile.TemporaryDirectory(prefix='hard-tile-guard-') as directory:
        temporary = Path(directory)
        mock = temporary / 'lake'
        mock.write_text('#!/bin/sh\ncat "$AXIOM_GUARD_FIXTURE"\n')
        mock.chmod(0o755)
        fixture = temporary / 'fixture.txt'
        environment = dict(os.environ, PATH=str(temporary) + os.pathsep + os.environ['PATH'],
                           AXIOM_GUARD_FIXTURE=str(fixture))
        for name, axioms, expected in CASES:
            fixture.write_text("'fixture' depends on axioms: " + axioms + '\n')
            result = subprocess.run(['bash', str(GUARD)], cwd=ROOT, env=environment,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True, timeout=60)
            (output / (name + '.log')).write_text(result.stdout)
            assert result.returncode == expected, (name, result.returncode, result.stdout)
            rows.append({'case': name, 'expected': expected, 'actual': result.returncode})
    receipt = {'status': 'actual_guard_allowlist_regressions_passed', 'rows': rows,
               'guard_sha256': hashlib.sha256(GUARD.read_bytes()).hexdigest(),
               'scope': 'synthetic parser fixtures; not a substitute for the real Lean audit'}
    (output / 'results.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(receipt['status'], len(rows), 'cases')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    run(parser.parse_args().output)
