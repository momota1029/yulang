#!/usr/bin/env python3
"""Bounded research observations; exits do not encode semantic pass/fail."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import time


ORACLE = '/tmp/yulang-hygiene-audit-my68a_85/target/debug/yulang'
ORACLE_SHA = 'f44bc8e41bc70290314e166832fa2a66183390ad742de458a60d7aabd39492fe'
NATIVE_SHA = 'ff9bbd6f0fb48200dcf691602547ab4020d0013e2b007b2493a2cc9a06293bed'
LIMIT = 256 * 1024


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    """Adapt visibility, handler layout and export naming, retaining computations."""
    result = {}
    for dialect in ('native', 'oracle'):
        oracle = dialect == 'oracle'
        export = 'our' if oracle else 'my'
        signal = ('pub act signal:\n    pub ping: () -> int\n\n' if oracle
                  else 'act signal:\n    our ping: () -> int\n\n')
        write = ('pub act write:\n    pub emit: () -> int\n\n' if oracle
                 else 'act write:\n    our emit: () -> int\n\n')

        def catch(expr, arm='1', operation='ping'):
            if oracle:
                return (f'catch {expr}:\n'
                        f'    signal::{operation}(), _ -> {arm}\n'
                        '    v -> v\n')
            return (f'catch {expr} {{\n'
                    f'    signal::{operation}(), _ -> {arm},\n'
                    '    v -> v\n}\n')

        def relay(parameter, expr):
            return f'{export} relay{parameter} = '+catch(expr)

        pure_value = ('catch 1:\n    v -> v\n' if oracle else
                      'catch 1 { v -> v }\n')
        result[dialect] = {
            '01-pure-value': f'{export} answer: [] int = '+pure_value,
            '02-direct-pure': signal+f'{export} answer: [] int = '
                              +catch('signal::ping()'),
            '03-omitted-callback': signal+relay(' cb', 'cb()')
                                   +f'{export} answer = relay signal::ping\n',
            '04-annotated-callback-pure': signal
                +relay('(cb: () -> [signal] int)', 'cb()')
                +f'{export} answer: [] int = relay signal::ping\n',
            '05-annotated-computation-pure': signal
                +relay('(thunk: [signal] int)', 'thunk')
                +f'{export} answer: [] int = relay signal::ping()\n',
            '06-write-residual': signal+write
                +relay('(thunk: [signal] int)', 'thunk')
                +f'{export} answer: [write] int = '
                 'relay ({ my ignored = write::emit(); signal::ping() })\n',
            '07-outside-arm': signal+f'{export} answer = '
                              +catch('signal::ping()', 'signal::ping()'),
            '08-same-family-other-operation':
                signal.replace('() -> int\n',
                    ('() -> int\n    pub pong: () -> int\n' if oracle else
                     '() -> int\n    our pong: () -> int\n'))
                +f'{export} answer = '+catch('signal::pong()'),
        }
        result[dialect]['03-omitted-callback-pure-check'] = (
            result[dialect]['03-omitted-callback'].replace(
                f'{export} answer =', f'{export} answer: [] int ='))
    return result


def observe(command, base):
    stdout, stderr = Path(str(base)+'.stdout'), Path(str(base)+'.stderr')
    started = time.monotonic()
    stopped = None
    with stdout.open('wb') as out, stderr.open('wb') as err:
        child = subprocess.Popen(command, stdout=out, stderr=err)
        while child.poll() is None:
            if time.monotonic()-started >= 15:
                stopped = 'timeout'
            elif stdout.stat().st_size+stderr.stat().st_size > LIMIT:
                stopped = 'output-cap'
            if stopped:
                child.kill()
                break
            time.sleep(0.01)
        status = child.wait()
    # Retain at most LIMIT bytes per stream even after a burst before poll.
    for path in (stdout, stderr):
        if path.stat().st_size > LIMIT:
            with path.open('r+b') as stream:
                stream.truncate(LIMIT)
            stopped = stopped or 'output-cap'
    return dict(command=command, exit=status, stopped=stopped,
                elapsed_seconds=round(time.monotonic()-started, 4),
                stdout=str(stdout), stderr=str(stderr),
                stdout_sha256=digest(stdout), stderr_sha256=digest(stderr),
                stdout_bytes=stdout.stat().st_size,
                stderr_bytes=stderr.stat().st_size)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--oracle', default=ORACLE)
    parser.add_argument('--native', default='target/debug/yu-playground')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--cases', nargs='*')
    parser.add_argument('--steps', nargs='+',
                        choices=['oracle-check', 'oracle-poly', 'oracle-run', 'native'])
    parser.add_argument('--budget', type=int, default=32)
    args = parser.parse_args()
    if not 1 <= args.budget <= 36:
        parser.error('budget must be 1..36 sequential CLI processes')
    oracle, native = Path(args.oracle).resolve(), Path(args.native).resolve()
    if digest(oracle) != ORACLE_SHA or digest(native) != NATIVE_SHA:
        parser.error('binary hash differs from pinned research baseline')
    root = args.out or Path(tempfile.mkdtemp(prefix='yulang-hygiene-oracle-comparison-'))
    root.mkdir(parents=True, exist_ok=True)
    manifest = root/'manifest.json'
    if manifest.exists():
        parser.error('output already contains manifest; choose a unique directory')
    paired = sources()
    names = args.cases or [name for name in paired['oracle'] if not name.endswith('-check')]
    if any(name not in paired['oracle'] for name in names):
        parser.error('unknown case')
    report = dict(oracle_commit='a58eefc31e22141574b6f20c6a5748151c6d79f1',
                  native_source_commit='e9790f96f154ef0ddf67cb45aa26a569148569d7',
                  oracle_sha256=digest(oracle), native_sha256=digest(native),
                  process_budget=args.budget, observations=[])
    for name in names:
        files = {}
        for dialect in ('oracle', 'native'):
            source = paired[dialect][name]
            assert len(source.encode()) <= 2048
            path = root/(name+'.'+dialect+'.yu')
            path.write_text(source)
            files[dialect] = path
        # Exported definitions are lazy. Force the designated value using a
        # final expression, which the native observation carrier cannot admit.
        runtime = root/(name+'.oracle-runtime.yu')
        runtime.write_text(paired['oracle'][name]+'\nanswer\n')
        assert runtime.stat().st_size <= 2048
        steps = [
            ('oracle-check', [str(oracle), '--no-prelude', '--no-cache',
                              'check', str(files['oracle'])]),
            ('oracle-poly', [str(oracle), '--no-prelude', '--no-cache',
                             'dump', str(files['oracle']), '--poly']),
            ('oracle-run', [str(oracle), '--no-prelude', '--no-cache',
                            'run', '--evidence-vm', '--print-roots',
                            str(runtime)]),
            ('native', [str(native), str(files['native'])]),
        ]
        for step, command in steps:
            if args.steps and step not in args.steps:
                continue
            if len(report['observations']) == args.budget:
                report['budget_exhausted'] = True
                break
            observation = observe(command, root/(name+'.'+step))
            observation.update(case=name, step=step,
                oracle_source_sha256=digest(files['oracle']),
                native_source_sha256=digest(files['native']),
                oracle_runtime_source_sha256=digest(runtime))
            report['observations'].append(observation)
            manifest.write_text(json.dumps(report, indent=2)+'\n')
            print(json.dumps(dict(case=name, step=step,
                  exit=observation['exit'], stopped=observation['stopped'])), flush=True)
        if report.get('budget_exhausted'):
            break
    print(str(manifest))


if __name__ == '__main__':
    main()
