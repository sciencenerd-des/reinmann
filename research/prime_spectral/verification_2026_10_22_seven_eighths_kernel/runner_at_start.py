"""Recheck the completed external adapter with Lean's fresh-environment checker.

Uses the existing build without compiling or changing any proof source. This is
Lean's own kernel replay, not a separately implemented external verifier.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

from minimal_replay import inputs, sha, TOOLCHAIN


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def compiled_bindings(search_paths):
    result = {}
    for base in search_paths:
        for path in sorted(base.rglob('*.olean*')):
            # Include exported, server and private module data, not sidecar hashes.
            if path.is_file() and not path.name.endswith('.hash'):
                result[str(path)] = dict(sha256=sha(path), bytes=path.stat().st_size)
    if not result:
        raise ValueError('No compiled objects found')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--timeout', type=int, default=1800)
    args = parser.parse_args()
    root, out = args.project.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, LEAN_NUM_THREADS='2')
    records = []

    def run(command, log_name):
        start = time.monotonic()
        with (out/log_name).open('w') as stream:
            try:
                proc = subprocess.run(command, cwd=root, env=env, stdout=stream,
                                      stderr=subprocess.STDOUT, timeout=args.timeout)
                status = proc.returncode
            except subprocess.TimeoutExpired:
                # The checker is launched directly, so timeout terminates it.
                status = 'timeout'
        records.append(dict(command=command, log=log_name, exit_code=status,
                            seconds=time.monotonic()-start, sha256=sha(out/log_name)))
        write_json(out/'commands.json', records)
        if status != 0:
            raise RuntimeError(f'Command failed ({status}); see {out/log_name}')
        return (out/log_name).read_text()

    before = inputs(root)
    write_json(out/'source_inputs.json', before)
    parent = root/'build-attempt-5'
    receipt = json.loads((parent/'receipt.json').read_text())
    if receipt['status'] != 'external_minimal_contract_built_and_standard_axiom_audited':
        raise ValueError('Existing successful build receipt required')
    if sha(parent/'BUILD_INPUTS.json') != receipt['input_manifest_sha256']:
        raise ValueError('Build input receipt mismatch')
    if json.loads((parent/'BUILD_INPUTS.json').read_text()) != before:
        raise ValueError('Current source inputs differ from completed build')
    path_text = run(['lake', 'env', 'printenv', 'LEAN_PATH'], 'search_path.log')
    env['LEAN_PATH'] = path_text.strip().splitlines()[-1]
    search_paths = [Path(p) for p in env['LEAN_PATH'].split(os.pathsep)]
    sysroot = Path(run(['lake', 'env', 'lean', '--print-prefix'],
                       'sysroot.log').strip().splitlines()[-1])
    checker = sysroot/'bin/leanchecker'
    checker_source = sysroot/'src/lean/LeanChecker.lean'
    (out/'LeanChecker.lean').write_bytes(checker_source.read_bytes())
    toolchain = run([str(sysroot/'bin/lean'), '--version'], 'toolchain.log')
    if 'version 4.34.1' not in toolchain:
        raise ValueError('Unexpected actual Lean version')
    print('Binding existing compiled objects before replay', flush=True)
    objects = compiled_bindings(search_paths)
    write_json(out/'compiled_objects.json', objects)
    print(f'Fresh kernel replay; {len(objects)} compiled data files bound', flush=True)
    checker_hash = sha(checker)
    run([str(checker), '--fresh', '--verbose', 'SevenEighths'], 'fresh_kernel.log')
    print('Fresh replay returned successfully; checking input stability', flush=True)
    if inputs(root) != before or compiled_bindings(search_paths) != objects:
        raise ValueError('Inputs changed during the replay')
    if sha(checker) != checker_hash:
        raise ValueError('Checker executable changed during the replay')
    audit = run([str(sysroot/'bin/lean'), 'SevenEighths.lean'], 'axioms.log')
    from minimal_replay import EXPECTED
    import re
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", audit)
    if len(rows) != 2 or {name for name, _ in rows} != EXPECTED:
        raise ValueError('Missing headline axiom reports')
    axioms = {name: sorted(value.replace(',', ' ').split()) for name, value in rows}
    if any(set(value)-{'propext', 'Classical.choice', 'Quot.sound'}
           for value in axioms.values()):
        raise ValueError('Nonstandard headline axiom')
    write_json(out/'result.json', dict(
        status='fresh_kernel_replay_succeeded_and_inputs_unchanged',
        upstream_commit=before['upstream_commit'], toolchain=TOOLCHAIN,
        target='SevenEighths', fresh_import_closure=True,
        checker_sha256=checker_hash, checker_source_sha256=sha(checker_source),
        prior_build_receipt_sha256=sha(parent/'receipt.json'),
        compiled_data_files_bound=len(objects), headline_axioms=axioms,
        runner_sha256=sha(Path(__file__)),
        scope='Lean own-kernel replay of all declarations imported by the adapter; '
              'not a separately implemented verifier, a new theorem, or an RH proof.'))
    write_json(out/'manifest.json', {str(p.relative_to(out)): sha(p)
                                    for p in sorted(out.rglob('*')) if p.is_file()})
    print('Fresh kernel replay and both standard-axiom reports passed', flush=True)


if __name__ == '__main__':
    main()
