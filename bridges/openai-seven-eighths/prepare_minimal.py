"""Fetch the pinned 7/8 theorem closure, without unrelated OpenAI libraries.

Uses upstream's exact manifest, selected requirements and two official patches.
Requires an installed Lean 4.34.1 toolchain, Git and network access. Does not run
lake update, change the main project, or claim that any proof has compiled.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time
import urllib.request

from minimal_replay import PIN, TOOLCHAIN, MANIFEST_SHA, CONFIG_SHA, PATCHES, HERE, imports, sha

BASE = f'https://raw.githubusercontent.com/openai/math/{PIN}/lean/'


def download(relative):
    for attempt in range(4):
        try:
            with urllib.request.urlopen(BASE+relative, timeout=45) as stream:
                return stream.read()
        except Exception:
            if attempt == 3:
                raise
            time.sleep(attempt+1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', required=True, type=Path, help='New external project directory')
    args = parser.parse_args()
    root = args.project.resolve()
    if shutil.disk_usage(root.parent).free < 12 * 1024**3:
        raise RuntimeError('Preparation requires at least 12 GiB free; no data was removed')
    subprocess.run(['lean', '+'+TOOLCHAIN, '--version'], check=True)
    root.mkdir(parents=True, exist_ok=False)
    (root/'lean-toolchain').write_text(TOOLCHAIN+'\n')
    config = HERE/'minimal-lakefile.lean'
    if sha(config) != CONFIG_SHA:
        raise ValueError('Unexpected minimal configuration bytes')
    shutil.copyfile(config, root/'lakefile.lean')
    shutil.copyfile(HERE/'SevenEighths.lean', root/'SevenEighths.lean')
    manifest_bytes = download('lake-manifest.json')
    if hashlib.sha256(manifest_bytes).hexdigest() != MANIFEST_SHA:
        raise ValueError('Upstream manifest hash differs')
    (root/'UPSTREAM_LAKE_MANIFEST.json').write_bytes(manifest_bytes)
    (root/'UPSTREAM_LAKEFILE.lean').write_bytes(download('lakefile.lean'))
    manifest = json.loads(manifest_bytes)
    manifest['name'] = 'QRHContract'
    (root/'lake-manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
    packages = root/'.lake/packages'
    packages.mkdir(parents=True)
    # Bootstrap these large dependencies shallowly at the exact resolved commits.
    for name in ['mathlib', 'PrimeNumberTheoremAnd', 'rellich-kondrachov']:
        item = next(x for x in manifest['packages'] if x['name'].strip('«»') == name)
        dep = packages/name
        dep.mkdir()
        subprocess.run(['git', 'init', '-q'], cwd=dep, check=True)
        subprocess.run(['git', 'remote', 'add', 'origin', item['url']], cwd=dep, check=True)
        subprocess.run(['git', 'fetch', '--depth', '1', 'origin', item['rev']], cwd=dep, check=True)
        subprocess.run(['git', 'checkout', '--detach', '-q', item['rev']], cwd=dep, check=True)
    (root/'patches').mkdir()
    applied = []
    for name, expected in PATCHES.items():
        relative = f'patches/{name}-lean4341.patch'
        patch = root/relative
        patch.write_bytes(download(relative))
        if sha(patch) != expected:
            raise ValueError(f'Upstream patch hash differs: {name}')
        subprocess.run(['git', 'apply', '--check', str(patch)], cwd=packages/name, check=True)
        subprocess.run(['git', 'apply', str(patch)], cwd=packages/name, check=True)
        applied.append(dict(package=name, patch_sha256=expected, source_url=BASE+relative))
    (root/'APPLIED_UPSTREAM_PATCHES.json').write_text(json.dumps(applied, indent=2)+'\n')
    seen, external = {}, set()
    pending = {'OAI.NumberTheory.DirichletL.Nonvanishing'}

    def fetch(name):
        relative = name.replace('.', '/')+'.lean'
        data = download(relative)
        path = root/relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return name, dict(sha256=sha(path), bytes=len(data), imports=imports(path))

    with ThreadPoolExecutor(max_workers=12) as pool:
        while pending:
            batch, pending = sorted(pending-set(seen)), set()
            for name, record in pool.map(fetch, batch):
                seen[name] = record
                for dependency in record['imports']:
                    if dependency.startswith('OAI.'):
                        pending.add(dependency)
                    else:
                        external.add(dependency)
            print('OpenAI source modules fetched:', len(seen), flush=True)
    if len(seen) != 2924:
        raise ValueError('Unexpected source closure size')
    source = dict(status='source_closure_fetched_not_built', upstream_commit=PIN,
                  files=len(seen), source_bytes=sum(x['bytes'] for x in seen.values()),
                  external_imports=sorted(external), modules=seen)
    (root/'SOURCE_CLOSURE.json').write_text(json.dumps(source, indent=2)+'\n')
    env = os.environ.copy()
    env['MATHLIB_NO_CACHE_ON_UPDATE'] = '1'
    subprocess.run(['lake', 'env', 'lean', '--version'], cwd=root, env=env, check=True)
    print('Prepared pinned sources and environment; no theorem build has been certified.', flush=True)


if __name__ == '__main__':
    main()
