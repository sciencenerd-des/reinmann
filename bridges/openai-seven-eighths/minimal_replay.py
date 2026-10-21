"""Replay the exact contract in a prepared, minimal upstream source closure.

This alternative to replay.py does not require the unrelated OpenAI libraries.
It never edits proof sources. prepare_minimal.py creates the pinned environment.
Only the final two explicit kernel axiom reports can issue a success receipt.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

PIN = '1581d4cbdd69a0faf34b2089614fe2a814316a6a'
TOOLCHAIN = 'leanprover/lean4:v4.34.1'
MANIFEST_SHA = 'cf6105a25d9dca2f166b241d9191bd12c7e13305890dc9c4d0952351cccc0794'
CONFIG_SHA = '38741523604016268bb8b68c3f282d14a6e5b9b5718cde94f529d85c86c3ff43'
PATCHES = {
    'PrimeNumberTheoremAnd': '0890432340c0025973bcfe070b634355fa366cc831595f68526e4c73c8903d82',
    'rellich-kondrachov': '0c121d8517dfeadc93ef24fe2deb56beec7cb3998e2552dee8f61c780b1408c8',
}
CACHED = {'Mathlib', 'Batteries', 'BatteriesRecycling', 'Aesop', 'Cli',
          'ImportGraph', 'LeanSearchClient', 'Plausible', 'Qq', 'ProofWidgets'}
BUILTIN = {'Lean', 'Init', 'Std', 'Lake'}
THEOREM = 'OAI.NumberTheory.DirichletL.Nonvanishing'
EXPECTED = {'OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re',
            'Reinmann.zetaZeroFreeRightOf_sevenEighths'}
HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stripped(source):
    """Remove nested comments while preserving original line numbers."""
    out, i, depth = [], 0, 0
    while i < len(source):
        if source[i:i+2] == '/-':
            depth += 1
            out.extend('  ')
            i += 2
        elif depth and source[i:i+2] == '-/':
            depth -= 1
            out.extend('  ')
            i += 2
        elif depth:
            out.append('\n' if source[i] == '\n' else ' ')
            i += 1
        elif source[i:i+2] == '--':
            j = source.find('\n', i)
            j = len(source) if j < 0 else j
            out.extend(' ' * (j-i))
            i = j
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError('Unclosed source comment')
    return ''.join(out)


def imports(path):
    result = []
    for line in stripped(path.read_text()).splitlines():
        match = re.match(r'^\s*(?:(?:public|private)\s+)?import\s+(.+)', line)
        if match:
            result.extend(match.group(1).split())
    return result


def inputs(root):
    if (root/'lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise ValueError('Unexpected toolchain')
    if sha(root/'UPSTREAM_LAKE_MANIFEST.json') != MANIFEST_SHA:
        raise ValueError('Upstream manifest differs from the pinned source')
    if sha(root/'lakefile.lean') != CONFIG_SHA:
        raise ValueError('Minimal package configuration changed')
    original = json.loads((root/'UPSTREAM_LAKE_MANIFEST.json').read_text())
    actual = json.loads((root/'lake-manifest.json').read_text())
    original['name'] = 'QRHContract'
    if actual != original:
        raise ValueError('Resolved manifest differs beyond the root package name')
    for item in actual['packages']:
        dep = root/'.lake/packages'/item['name'].strip('«»')
        if dep.exists() and item['type'] == 'git':
            head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=dep,
                                           text=True).strip()
            if head != item['rev']:
                raise ValueError(f'Dependency revision differs: {dep.name}')
    for name, expected in PATCHES.items():
        patch = root/'patches'/f'{name}-lean4341.patch'
        if sha(patch) != expected:
            raise ValueError(f'Unexpected upstream compatibility patch: {name}')
        subprocess.run(['git', 'apply', '--reverse', '--check', str(patch)],
                       cwd=root/'.lake/packages'/name, check=True,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    state = json.loads((root/'SOURCE_CLOSURE.json').read_text())
    if state['upstream_commit'] != PIN or len(state['modules']) != 2924:
        raise ValueError('Unexpected OpenAI source closure')
    for name, item in state['modules'].items():
        path = root/(name.replace('.', '/')+'.lean')
        if sha(path) != item['sha256'] or imports(path) != item['imports']:
            raise ValueError(f'OpenAI source changed: {name}')
    if (root/'SevenEighths.lean').read_bytes() != (HERE/'SevenEighths.lean').read_bytes():
        raise ValueError('Contract differs from the repository adapter')
    graph, cached, files = {}, set(), {}
    pending = [THEOREM]
    packages = list((root/'.lake/packages').iterdir())
    while pending:
        name = pending.pop()
        prefix = name.split('.')[0]
        if prefix in BUILTIN:
            continue
        if prefix in CACHED:
            cached.add(name)
            continue
        if name in graph:
            continue
        relative = name.replace('.', '/')+'.lean'
        paths = [base/relative for base in [root, *packages] if (base/relative).is_file()]
        if len(paths) != 1:
            raise ValueError(f'Missing or ambiguous module: {name}')
        path = paths[0]
        # This is a preflight, not a substitute for the final semantic audit.
        if re.search(r'\b(sorry|admit|sorryAx|native_decide|axiom)\b', stripped(path.read_text())):
            raise ValueError(f'Admission/custom-axiom token in imported source: {name}')
        graph[name] = imports(path)
        files[str(path.relative_to(root))] = sha(path)
        pending.extend(graph[name])
    return dict(upstream_commit=PIN, modules=graph, source_sha256=files,
                cache_roots=sorted(cached), configuration_sha256={
                    name: sha(root/name) for name in
                    ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'SevenEighths.lean']},
                patches_sha256=PATCHES)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path, help='New receipt directory')
    parser.add_argument('--check-only', action='store_true')
    parser.add_argument('--batch-size', type=int, default=2, choices=range(1, 9))
    parser.add_argument('--resume', type=Path, action='append', default=[],
                        help='Prior compatible build attempt; repeat for parent attempts')
    parser.add_argument('--compact-setups', action='store_true',
                        help='Losslessly archive completed OAI setup scratch between batches')
    args = parser.parse_args()
    root, output = args.project.resolve(), args.output.resolve()
    checked = inputs(root)
    completed = set()
    resume_records = []
    for attempt in args.resume:
        previous = json.loads((attempt/'BUILD_INPUTS.json').read_text())
        if any(previous[key] != checked[key] for key in ['modules', 'source_sha256', 'cache_roots']):
            raise ValueError('Resume source graph differs')
        prior_commands = json.loads((attempt/'commands.json').read_text())
        resume_records.append(dict(attempt=str(attempt.resolve()),
                                   input_manifest_sha256=sha(attempt/'BUILD_INPUTS.json'),
                                   commands_sha256=sha(attempt/'commands.json'),
                                   commands=prior_commands))
        for record in prior_commands:
            if record['exit_code'] or sha(attempt/record['log']) != record['log_sha256']:
                raise ValueError('Failed or changed command in resume receipt')
            command = record['command']
            if command[:3] == ['lake', '--log-level=error', 'build']:
                completed.update(command[3:])
    output.mkdir(parents=True, exist_ok=False)
    (output/'BUILD_INPUTS.json').write_text(json.dumps(checked, indent=2)+'\n')
    (output/'RESUME.json').write_text(json.dumps(resume_records, indent=2)+'\n')
    (output/'runner_at_start.py').write_bytes(Path(__file__).read_bytes())
    compactor = HERE/'compact_setups.py'
    compactor_sha = sha(compactor) if args.compact_setups else None
    print(f'Checked {len(checked["modules"])} source modules; {len(completed)} completed previously',
          flush=True)
    if args.check_only:
        return
    env = os.environ.copy()
    env.update(MATHLIB_CACHE_DIR=str(root/'mathlib-cache'), MATHLIB_NO_CACHE_ON_UPDATE='1',
               LEAN_NUM_THREADS='2')
    records = []

    def run(command, name):
        if shutil.disk_usage(root).free < 4 * 1024**3:
            raise RuntimeError('Stopped before next command: less than 4 GiB free')
        start = time.monotonic()
        with (output/name).open('w') as stream:
            result = subprocess.run(command, cwd=root, env=env, stdout=stream,
                                    stderr=subprocess.STDOUT)
        records.append(dict(command=command, log=name, exit_code=result.returncode,
                            elapsed_seconds=time.monotonic()-start, log_sha256=sha(output/name)))
        (output/'commands.json').write_text(json.dumps(records, indent=2)+'\n')
        if result.returncode:
            raise RuntimeError(f'Command failed; see {output/name}')

    run(['lake', 'env', 'lean', '--version'], 'toolchain.log')
    if 'version 4.34.1' not in (output/'toolchain.log').read_text():
        raise RuntimeError('Wrong actual compiler version')
    run(['lake', 'exe', 'cache', 'get', *checked['cache_roots']], 'mathlib-cache.log')
    pending = set(checked['modules'])-completed
    step = 0

    def compact():
        if sha(compactor) != compactor_sha:
            raise RuntimeError('Scratch compactor changed during build')
        command = [sys.executable, str(compactor), '--project', str(root)]
        for attempt in [*args.resume, output]:
            command.extend(['--attempt', str(attempt)])
        command.extend(['--output', str(output/f'compaction-{step:04}.json')])
        run(command, f'compaction-{step:04}.log')

    while pending:
        ready = sorted(name for name in pending if not set(checked['modules'][name]) & pending)
        if not ready:
            raise RuntimeError('Dependency cycle')
        batch = ready[:args.batch_size]
        run(['lake', '--log-level=error', 'build', *batch], f'batch-{step:04}.log')
        pending.difference_update(batch)
        step += 1
        progress = dict(status='building_source_closure', total=len(checked['modules']),
                        built=len(checked['modules'])-len(pending), remaining=len(pending),
                        last_targets=batch)
        (output/'progress.json').write_text(json.dumps(progress, indent=2)+'\n')
        if step % 10 == 0 or not pending:
            print(json.dumps(progress), flush=True)
        if args.compact_setups and (step % 20 == 0 or shutil.disk_usage(root).free < 6 * 1024**3):
            compact()
    run(['lake', 'build', 'SevenEighths'], 'adapter-build.log')
    run(['lake', 'env', 'lean', 'SevenEighths.lean'], 'adapter-audit.log')
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",
                      (output/'adapter-audit.log').read_text())
    if len(rows) != 2 or {name for name, _ in rows} != EXPECTED:
        raise RuntimeError('Expected both theorem axiom reports')
    if any(set(axioms.replace(',', ' ').split())-{'propext', 'Classical.choice', 'Quot.sound'}
           for _, axioms in rows):
        raise RuntimeError('Headline theorem uses a nonstandard axiom')
    # Recheck proof/configuration bytes after the build, not just before it.
    if inputs(root) != checked:
        raise RuntimeError('Inputs changed during compilation')
    receipt = dict(status='external_minimal_contract_built_and_standard_axiom_audited',
                   upstream_commit=PIN, toolchain=TOOLCHAIN,
                   source_modules=len(checked['modules']),
                   input_manifest_sha256=sha(output/'BUILD_INPUTS.json'),
                   commands_sha256=sha(output/'commands.json'),
                   runner_sha256=sha(output/'runner_at_start.py'),
                   resume_manifest_sha256=sha(output/'RESUME.json'),
                   compactor_sha256=compactor_sha,
                   resumed_from=[str(p.resolve()) for p in args.resume],
                   scope='External 4.34.1 contract only; no unconditional PF58 in Lean 4.30.')
    (output/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(receipt['status'], flush=True)


if __name__ == '__main__':
    main()
