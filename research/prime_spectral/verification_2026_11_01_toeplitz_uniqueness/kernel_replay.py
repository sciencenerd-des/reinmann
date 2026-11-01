"""Record a fresh Lean own-kernel replay, reusing immutable baseline input hashes."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]
BASE = ROOT/'research/prime_spectral/verification_2026_11_01_toeplitz_kernel'


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for b in iter(lambda: stream.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def main():
    if (PACKET/'manifest.json').exists():
        raise RuntimeError('Sealed packet; replay with lake env leanchecker --fresh Reinmann.ToeplitzUniqueness')
    env = dict(os.environ, LEAN_NUM_THREADS='2')
    leanpath = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT,
                                      text=True).strip().splitlines()[-1]
    sysroot = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'], cwd=ROOT,
                                         text=True).strip().splitlines()[-1])
    env['LEAN_PATH'] = leanpath
    bases = [Path(p) if Path(p).is_absolute() else ROOT/p for p in leanpath.split(os.pathsep)]
    bases.append(sysroot/'lib/lean')
    pending = ['Reinmann.ToeplitzUniqueness', 'Init']
    modules, paths = {}, set()
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        relative = Path(*module.split('.')).with_suffix('.ilean')
        hits = [b/relative for b in bases if (b/relative).is_file()]
        if not hits:
            raise RuntimeError(f'No import metadata: {module}')
        metadata = hits[0]
        imports = json.loads(metadata.read_text())['directImports']
        modules[module] = {'metadata': str(metadata), 'imports': [i[0] for i in imports]}
        paths.add(metadata)
        for suffix in ('.olean', '.olean.server', '.olean.private'):
            compiled = metadata.with_suffix(suffix)
            if compiled.is_file():
                paths.add(compiled)
        pending.extend(i[0] for i in imports)
    before = {str(p): {'sha256': sha(p), 'bytes': p.stat().st_size} for p in sorted(paths)}
    old_inputs = json.loads((BASE/'compiled_inputs.json').read_text())
    old_imports = json.loads((BASE/'compiled_imports.json').read_text())
    for name, record in old_inputs.items():
        if before.get(name) != record:
            raise RuntimeError(f'Baseline compiled input drift: {name}')
    for name, record in old_imports.items():
        if modules.get(name) != record:
            raise RuntimeError(f'Baseline import drift: {name}')
    for name, current, old in [('compiled_inputs', before, old_inputs),
                               ('compiled_imports', modules, old_imports)]:
        data = {'baseline': str((BASE/(name+'.json')).relative_to(ROOT)),
                'baseline_sha256': sha(BASE/(name+'.json')),
                'added': {k: v for k, v in current.items() if k not in old},
                'total_entries': len(current)}
        (PACKET/(name+'_delta.json')).write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')
    sources = {name: sha(ROOT/name) for name in
               ['Reinmann/ToeplitzKernel.lean', 'Reinmann/ToeplitzSimpleRoots.lean',
                'Reinmann/ToeplitzAtomic.lean', 'Reinmann/ToeplitzExtension.lean',
                'Reinmann/ToeplitzDowndate.lean', 'Reinmann/ToeplitzRepresentation.lean', 'Reinmann/ToeplitzUniqueness.lean', 'lean-toolchain', 'lake-manifest.json']}
    checker = sysroot/'bin/leanchecker'
    checker_hash = sha(checker)
    command = [str(checker), '--fresh', '--verbose', 'Reinmann.ToeplitzUniqueness']
    print(f'Replaying {len(modules)} modules; {len(before)} input files; '
          f'{len(before)-len(old_inputs)} additions to the immutable baseline', flush=True)
    with (PACKET/'fresh_kernel.log').open('w') as log:
        run = subprocess.run(command, cwd=ROOT, env=env, stdout=log,
                             stderr=subprocess.STDOUT, timeout=600)
    if run.returncode:
        raise RuntimeError(f'Fresh replay failed: {run.returncode}')
    for name, record in before.items():
        if sha(Path(name)) != record['sha256']:
            raise RuntimeError(f'Compiled input changed: {name}')
    for name, digest in sources.items():
        if sha(ROOT/name) != digest:
            raise RuntimeError(f'Source changed: {name}')
    if sha(checker) != checker_hash:
        raise RuntimeError('Checker changed')
    receipt = {'command': command, 'exit_code': 0, 'modules_bound': len(modules),
               'compiled_and_metadata_files_bound': len(before),
               'baseline_files_reused': len(old_inputs), 'added_files': len(before)-len(old_inputs),
               'checker_sha256': checker_hash, 'runner_sha256': sha(Path(__file__)),
               'source_sha256': sources, 'bound_inputs_unchanged': True,
               'scope': 'Lean own-kernel fresh replay; not an independently implemented verifier.'}
    (PACKET/'kernel_replay.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print('Fresh Lean kernel replay passed; all source/compiled bindings unchanged', flush=True)


if __name__ == '__main__':
    main()
