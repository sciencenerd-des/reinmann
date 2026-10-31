"""Replay this standalone module and its imports with Lean's own fresh kernel.

Requires the recorded Lean 4.30 build. This is not an independent verifier.
The .ilean import graph identifies the compiled closure whose bytes are bound.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess

PACKET = Path(__file__).resolve().parent
ROOT = PACKET.parents[2]


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def main():
    if (PACKET/'manifest.json').exists():
        raise RuntimeError('Packet is sealed; use validate.py --replay-kernel for read-only replay')
    env = dict(os.environ, LEAN_NUM_THREADS='2')
    leanpath = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=ROOT,
                                      text=True).strip().splitlines()[-1]
    sysroot = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'], cwd=ROOT,
                                         text=True).strip().splitlines()[-1])
    env['LEAN_PATH'] = leanpath
    bases = [Path(p) if Path(p).is_absolute() else ROOT/p for p in leanpath.split(os.pathsep)]
    bases.append(sysroot/'lib/lean')
    pending = ['Reinmann.ToeplitzKernel', 'Init']
    modules, paths = {}, set()
    while pending:
        module = pending.pop()
        if module in modules:
            continue
        relative = Path(*module.split('.'))
        hits = [b/relative.with_suffix('.ilean') for b in bases
                if (b/relative.with_suffix('.ilean')).is_file()]
        if not hits:
            raise RuntimeError(f'No import metadata for {module}')
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
    (PACKET/'compiled_inputs.json').write_text(json.dumps(before, indent=2)+'\n')
    (PACKET/'compiled_imports.json').write_text(json.dumps(modules, indent=2, sort_keys=True)+'\n')
    checker = sysroot/'bin/leanchecker'
    source = sysroot/'src/lean/LeanChecker.lean'
    checker_hash = sha(checker)
    command = [str(checker), '--fresh', '--verbose', 'Reinmann.ToeplitzKernel']
    print(f'Replaying {len(modules)} modules; {len(before)} compiled/metadata files bound', flush=True)
    with (PACKET/'fresh_kernel.log').open('w') as log:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=log,
                                stderr=subprocess.STDOUT, timeout=600)
    if result.returncode:
        raise RuntimeError(f'Kernel replay failed ({result.returncode})')
    for name, record in before.items():
        if sha(Path(name)) != record['sha256']:
            raise RuntimeError(f'Compiled input changed: {name}')
    if sha(checker) != checker_hash:
        raise RuntimeError('Checker changed')
    receipt = {'command': command, 'exit_code': result.returncode,
               'import_modules_bound': len(modules), 'compiled_and_metadata_files_bound': len(before),
               'checker_sha256': checker_hash, 'checker_source_sha256': sha(source),
               'compiled_inputs_unchanged': True,
               'scope': 'Lean own-kernel fresh replay; not an independently implemented verifier.'}
    (PACKET/'kernel_replay.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print('Fresh kernel replay passed; bound compiled inputs unchanged', flush=True)


if __name__ == '__main__':
    main()
