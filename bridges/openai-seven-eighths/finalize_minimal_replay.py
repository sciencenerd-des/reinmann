"""Verify and preserve a completed external seven-eighths replay.

This refuses an unfinished build before creating an output directory. It checks
the exact contract, all resumed build logs and source coverage. The resulting
packet contains licensed source, pinned configuration and compressed raw logs.
It does not import external binaries into the Lean 4.30 development.
"""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path
import re
import tarfile
import urllib.request

from minimal_replay import EXPECTED, HERE, PIN, TOOLCHAIN, inputs, sha

LICENSE_SHA = 'c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4'


def checked_audit(text):
    rows = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)
    if len(rows) != 2 or {name for name, _ in rows} != EXPECTED:
        raise ValueError('Both exact theorem axiom reports are required')
    for name, axioms in rows:
        if set(axioms.replace(',', ' ').split())-{'propext', 'Classical.choice', 'Quot.sound'}:
            raise ValueError(f'Nonstandard theorem axiom: {name}: {axioms}')
    return {name: axioms.replace(',', ' ').split() for name, axioms in rows}


def checked_build(project, attempt):
    receipt_file = attempt/'receipt.json'
    if not receipt_file.is_file():
        raise ValueError('External proof incomplete: no successful final build receipt')
    receipt = json.loads(receipt_file.read_text())
    if receipt['status'] != 'external_minimal_contract_built_and_standard_axiom_audited':
        raise ValueError('A successful exact-contract receipt is required')
    assert receipt['upstream_commit'] == PIN and receipt['toolchain'] == TOOLCHAIN
    current = inputs(project)
    saved = json.loads((attempt/'BUILD_INPUTS.json').read_text())
    assert current == saved
    for field, name in [('input_manifest_sha256', 'BUILD_INPUTS.json'),
                        ('commands_sha256', 'commands.json'),
                        ('runner_sha256', 'runner_at_start.py'),
                        ('resume_manifest_sha256', 'RESUME.json')]:
        assert receipt[field] == sha(attempt/name), field
    assert receipt['runner_sha256'] == sha(HERE/'minimal_replay.py')
    assert receipt['compactor_sha256'] == sha(HERE/'compact_setups.py')
    history = json.loads((attempt/'RESUME.json').read_text())
    attempts, completed = [], set()
    for parent in history:
        path = Path(parent['attempt']).resolve()
        if path.parent != project or not re.fullmatch(r'build-attempt-\d+', path.name):
            raise ValueError('Unexpected resumed build directory')
        assert parent['input_manifest_sha256'] == sha(path/'BUILD_INPUTS.json')
        assert parent['commands_sha256'] == sha(path/'commands.json')
        assert parent['commands'] == json.loads((path/'commands.json').read_text())
        previous = json.loads((path/'BUILD_INPUTS.json').read_text())
        for key in ['modules', 'source_sha256', 'cache_roots']:
            assert previous[key] == current[key], (path.name, key)
        attempts.append(path)
    attempts.append(attempt)
    for path in attempts:
        for command in json.loads((path/'commands.json').read_text()):
            log = command['log']
            if Path(log).name != log or not log.endswith('.log'):
                raise ValueError('Unexpected command log path')
            assert command['exit_code'] == 0 and command['log_sha256'] == sha(path/log)
            argv = command['command']
            if argv[:3] == ['lake', '--log-level=error', 'build']:
                assert set(argv[3:]) <= set(current['modules'])
                completed.update(argv[3:])
    assert completed == set(current['modules']), 'Incomplete source-build history'
    assert len(completed) == receipt['source_modules'] == 2943
    assert len([name for name in completed if name.startswith('OAI.')]) == 2924
    assert 'version 4.34.1' in (attempt/'toolchain.log').read_text()
    audit = checked_audit((attempt/'adapter-audit.log').read_text())
    assert (project/'SevenEighths.lean').read_bytes() == (HERE/'SevenEighths.lean').read_bytes()
    return current, attempts, audit


def source_archive(project, source_inputs, destination):
    files = {f'project/{name}': project/name for name in source_inputs['source_sha256']}
    for name in ['lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'SevenEighths.lean',
                 'UPSTREAM_LAKE_MANIFEST.json', 'UPSTREAM_LAKEFILE.lean',
                 'SOURCE_CLOSURE.json', 'APPLIED_UPSTREAM_PATCHES.json']:
        files['project/'+name] = project/name
    files['project/LICENSE'] = project/'UPSTREAM_LICENSE'
    for package in ['PrimeNumberTheoremAnd', 'rellich-kondrachov']:
        files[f'project/.lake/packages/{package}/LICENSE'] = project/'.lake/packages'/package/'LICENSE'
        name = f'patches/{package}-lean4341.patch'
        files['project/'+name] = project/name
    for name in ['minimal_replay.py', 'prepare_minimal.py', 'compact_setups.py',
                 'finalize_minimal_replay.py', 'minimal-lakefile.lean',
                 'SevenEighths.lean', 'MINIMAL_REPLAY.md']:
        files['reproducer/'+name] = HERE/name
    for candidate in [HERE/'LICENSE', HERE.parents[1]/'LICENSE']:
        if candidate.is_file():
            files['reproducer/LICENSE'] = candidate
            break
    manifest = dict(upstream_commit=PIN, toolchain=TOOLCHAIN,
                    source_modules=2943, OAI_source_modules=2924,
                    files_sha256={name: sha(path) for name, path in sorted(files.items())},
                    scope='Source and configuration. Mathlib binaries are fetched from pinned caches.')
    with destination.open('xb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode='w') as archive:
            data_files = {name: path.read_bytes() for name, path in files.items()}
            data_files['SOURCE_MANIFEST.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
            for name, data in sorted(data_files.items()):
                info = tarfile.TarInfo(name)
                info.size, info.mode, info.mtime = len(data), 0o644, 0
                archive.addfile(info, io.BytesIO(data))
    # Verify every archived source byte, without extracting archive paths.
    with tarfile.open(destination, 'r:gz') as archive:
        assert all(item.isfile() for item in archive.getmembers())
        assert set(archive.getnames()) == set(manifest['files_sha256']) | {'SOURCE_MANIFEST.json'}
        for name, wanted in manifest['files_sha256'].items():
            assert hashlib.sha256(archive.extractfile(name).read()).hexdigest() == wanted
    return manifest


def history_archive(attempts, destination):
    files = {}
    for path in attempts:
        names = {'BUILD_INPUTS.json', 'commands.json'}
        commands_bytes = (path/'commands.json').read_bytes()
        names.update(command['log'] for command in json.loads(commands_bytes))
        names.update(name for name in ['receipt.json', 'RESUME.json', 'runner_at_start.py', 'STOPPED.json']
                     if (path/name).is_file())
        for name in sorted(names):
            files[f'attempts/{path.name}/{name}'] = commands_bytes if name == 'commands.json' else (path/name).read_bytes()
    manifest = dict(attempts=[path.name for path in attempts],
                    files_sha256={name: hashlib.sha256(data).hexdigest()
                                  for name, data in sorted(files.items())})
    files['HISTORY_MANIFEST.json'] = (json.dumps(manifest, indent=2)+'\n').encode()
    with destination.open('xb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', mtime=0) as compressed:
        with tarfile.open(fileobj=compressed, mode='w') as archive:
            for name, data in sorted(files.items()):
                info = tarfile.TarInfo(name)
                info.size, info.mode, info.mtime = len(data), 0o644, 0
                archive.addfile(info, io.BytesIO(data))
    return manifest


def finalize(project, attempt, output):
    project, attempt, output = project.resolve(), attempt.resolve(), output.resolve()
    source_inputs, attempts, audit = checked_build(project, attempt)
    license_file = project/'UPSTREAM_LICENSE'
    if not license_file.exists():
        with urllib.request.urlopen(f'https://raw.githubusercontent.com/openai/math/{PIN}/LICENSE',
                                    timeout=30) as response:
            data = response.read()
        assert hashlib.sha256(data).hexdigest() == LICENSE_SHA
        license_file.write_bytes(data)
    assert sha(license_file) == LICENSE_SHA
    # All proof gates above run before any candidate packet is written.
    output.mkdir(parents=True, exist_ok=False)
    (output/'build_inputs.json').write_text(json.dumps(source_inputs, indent=2)+'\n')
    history_file = output/'build-history.tar.gz'
    history = history_archive(attempts, history_file)
    archive = output/'seven-eighths-source-1581d4c.tar.gz'
    source_manifest = source_archive(project, source_inputs, archive)
    result = dict(status='external_seven_eighths_exact_contract_rebuilt_and_receipt_verified',
                  upstream_commit=PIN, toolchain=TOOLCHAIN, source_modules=2943,
                  OAI_source_modules=2924, headline_axioms=audit,
                  source_archive_sha256=sha(archive), source_archive_files=len(source_manifest['files_sha256']),
                  build_history_sha256=sha(history_file), history_files=len(history['files_sha256']),
                  local_Lean430_PF58_unconditional=False,
                  scope='External Lean 4.34.1 replay; local Lean 4.30 PF58 retains its named external input.')
    (output/'result.json').write_text(json.dumps(result, indent=2)+'\n')
    (output/'README.md').write_text(
        '# External seven-eighths proof replay\n\n'
        f'Upstream: https://github.com/openai/math/tree/{PIN}\n\n'
        f'Toolchain: `{TOOLCHAIN}`. All 2,943 source modules outside the pinned '
        'Mathlib cache are covered by the retained successful command history. '
        'The source archive contains the 2,924 OpenAI modules, 19 dependency '
        'modules, official compatibility patches, exact configuration and licenses.\n\n'
        'The two kernel axiom reports cover the upstream theorem and the exact '
        '`Reinmann.ZetaZeroFreeRightOf (7/8)` adapter. The main Lean 4.30 project '
        'continues to carry the named external input in its PF58 theorem.\n\n'
        'Verify packet integrity with:\n\n'
        '```sh\npython3 bridges/openai-seven-eighths/finalize_minimal_replay.py '
        '--verify-packet /absolute/path/to/packet\n```\n\n'
        'Packet verification checks retained evidence. A fresh kernel rebuild '
        'uses `prepare_minimal.py` and `minimal_replay.py` in a new external '
        'directory as described in the archived reproduction instructions.\n')
    bindings = {str(path.relative_to(output)): sha(path) for path in output.rglob('*') if path.is_file()}
    (output/'manifest.json').write_text(json.dumps(dict(artifacts_sha256=bindings), indent=2)+'\n')
    verify_packet(output)
    print(result['status'])


def verify_packet(output):
    bindings = json.loads((output/'manifest.json').read_text())['artifacts_sha256']
    assert all(not Path(name).is_absolute() and '..' not in Path(name).parts for name in bindings)
    assert all(sha(output/name) == wanted for name, wanted in bindings.items())
    result = json.loads((output/'result.json').read_text())
    assert result['upstream_commit'] == PIN and result['toolchain'] == TOOLCHAIN
    assert result['status'] == 'external_seven_eighths_exact_contract_rebuilt_and_receipt_verified'
    assert result['local_Lean430_PF58_unconditional'] is False
    assert set(result['headline_axioms']) == EXPECTED
    assert all(set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}
               for axioms in result['headline_axioms'].values())
    covered = set()
    audit_reports = 0
    history_file = output/'build-history.tar.gz'
    assert sha(history_file) == result['build_history_sha256']
    with tarfile.open(history_file, 'r:gz') as tar:
        assert all(item.isfile() for item in tar.getmembers())
        history = json.loads(tar.extractfile('HISTORY_MANIFEST.json').read())
        assert set(tar.getnames()) == set(history['files_sha256']) | {'HISTORY_MANIFEST.json'}
        for name, wanted in history['files_sha256'].items():
            assert hashlib.sha256(tar.extractfile(name).read()).hexdigest() == wanted
        for attempt_name in history['attempts']:
            prefix = f'attempts/{attempt_name}/'
            for record in json.loads(tar.extractfile(prefix+'commands.json').read()):
                raw = tar.extractfile(prefix+record['log']).read()
                assert hashlib.sha256(raw).hexdigest() == record['log_sha256']
                assert record['exit_code'] == 0
                if record['command'][:3] == ['lake', '--log-level=error', 'build']:
                    covered.update(record['command'][3:])
            if prefix+'adapter-audit.log' in history['files_sha256']:
                assert checked_audit(tar.extractfile(prefix+'adapter-audit.log').read().decode()) == result['headline_axioms']
                audit_reports += 1
    assert audit_reports == 1
    source_inputs = json.loads((output/'build_inputs.json').read_text())
    assert covered == set(source_inputs['modules']) and len(covered) == 2943
    archive = output/'seven-eighths-source-1581d4c.tar.gz'
    assert sha(archive) == result['source_archive_sha256']
    with tarfile.open(archive, 'r:gz') as tar:
        assert all(item.isfile() for item in tar.getmembers())
        source = json.loads(tar.extractfile('SOURCE_MANIFEST.json').read())
        assert source['upstream_commit'] == PIN and source['source_modules'] == 2943
        assert set(tar.getnames()) == set(source['files_sha256']) | {'SOURCE_MANIFEST.json'}
        for name, wanted in source['files_sha256'].items():
            assert hashlib.sha256(tar.extractfile(name).read()).hexdigest() == wanted
        for name, wanted in source_inputs['source_sha256'].items():
            assert source['files_sha256']['project/'+name] == wanted
        assert tar.extractfile('project/SevenEighths.lean').read() == (HERE/'SevenEighths.lean').read_bytes()
    print('Verified external replay packet:', len(bindings), 'bindings; 2943 source modules')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path)
    parser.add_argument('--attempt', type=Path)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--verify-packet', type=Path)
    args = parser.parse_args()
    if args.verify_packet:
        verify_packet(args.verify_packet.resolve())
    elif args.project and args.attempt and args.output:
        finalize(args.project, args.attempt, args.output)
    else:
        parser.error('Supply --verify-packet, or --project, --attempt and --output')
