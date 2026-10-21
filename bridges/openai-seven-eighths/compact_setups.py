"""Losslessly archive completed modules' generated Lake setup JSON files.

Only root-project OAI scratch files named by successful checksum-bound build
commands are eligible. No proof source, compiled artifact, dependency cache or
unfinished target is removed. Archives are read back before originals are
unlinked. Use --restore RECEIPT to restore the exact original bytes and mtime.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', required=True, type=Path)
    parser.add_argument('--attempt', action='append', type=Path, default=[])
    parser.add_argument('--output', type=Path, help='New compaction receipt')
    parser.add_argument('--restore', type=Path, help='Previously written compaction receipt')
    args = parser.parse_args()
    root = args.project.resolve()
    scratch = root/'.lake/build/ir/OAI'
    if args.restore:
        receipt = json.loads(args.restore.read_text())
        for record in receipt['files']:
            path = root/record['path']
            if not path.resolve().is_relative_to(scratch.resolve()):
                raise ValueError('Restore path outside owned OAI scratch directory')
            archive = path.with_suffix(path.suffix+'.gz')
            data = gzip.decompress(archive.read_bytes())
            if digest(data) != record['sha256']:
                raise ValueError(f'Archive hash differs: {archive}')
            if path.exists() and path.read_bytes() != data:
                raise ValueError(f'Preserving different existing file: {path}')
            path.write_bytes(data)
            os.utime(path, ns=(record['mtime_ns'], record['mtime_ns']))
        print('Restored exact scratch bytes:', len(receipt['files']))
        return
    if not args.attempt or args.output is None or args.output.exists():
        parser.error('Compaction needs --attempt and a new --output')
    eligible, bindings = set(), {}
    for attempt in args.attempt:
        commands = attempt/'commands.json'
        snapshot = commands.read_bytes()
        records = json.loads(snapshot)
        bindings[str(commands.resolve())] = dict(sha256=digest(snapshot), commands=records)
        for record in records:
            if record['exit_code'] or digest((attempt/record['log']).read_bytes()) != record['log_sha256']:
                raise ValueError('Failed or modified build command')
            command = record['command']
            if command[:3] == ['lake', '--log-level=error', 'build']:
                eligible.update(name for name in command[3:]
                                if re.fullmatch(r'OAI(?:\.[A-Za-z0-9_]+)+', name))
    files = []
    for name in sorted(eligible):
        path = root/'.lake/build/ir'/(name.replace('.', '/')+'.setup.json')
        if not path.exists():
            continue
        if path.is_symlink() or not path.resolve().is_relative_to(scratch.resolve()):
            raise ValueError('Scratch path escapes owned directory')
        data = path.read_bytes()
        archive = path.with_suffix(path.suffix+'.gz')
        if archive.exists():
            if gzip.decompress(archive.read_bytes()) != data:
                raise ValueError(f'Preserving different archive: {archive}')
        else:
            with archive.open('xb') as stream:
                stream.write(gzip.compress(data, mtime=0))
        if gzip.decompress(archive.read_bytes()) != data:
            raise ValueError('Archive readback differs')
        files.append(dict(path=str(path.relative_to(root)), bytes=len(data),
                          sha256=digest(data), gzip_bytes=archive.stat().st_size,
                          gzip_sha256=digest(archive.read_bytes()), mtime_ns=path.stat().st_mtime_ns))
    # Retain recovery metadata before removing any generated original.
    receipt = dict(status='completed_OAI_setup_scratch_losslessly_archived',
                   command_snapshots_sha256=bindings, files=files,
                   bytes_saved=sum(x['bytes']-x['gzip_bytes'] for x in files),
                   scope='Generated setup JSON only. This is not proof verification.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('x') as stream:
        stream.write(json.dumps(receipt, indent=2)+'\n')
    for record in files:
        path = root/record['path']
        if digest(path.read_bytes()) != record['sha256']:
            raise ValueError(f'Scratch changed before removal: {path}')
        path.unlink()
    print('Archived setup files:', len(files), '; saved bytes:', receipt['bytes_saved'])


if __name__ == '__main__':
    main()
