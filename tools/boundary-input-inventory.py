#!/usr/bin/env python3
"""Inventory import reachability and ledger mentions; not semantic input coverage.

Run from any directory. --check compares the committed TSV with current sources.
Only repository Lean sources are read; build caches and external packages are not.
"""
from pathlib import Path
import argparse
import hashlib
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / 'notes/design/2026-11-10-boundary-inputs-ledger.md'
OUTPUT = ROOT / 'notes/design/2026-11-10-boundary-input-coverage.tsv'


def uncomment(text):
    """Preserve newlines while removing nested Lean comments and string bodies."""
    result = []
    depth = 0
    string = False
    i = 0
    while i < len(text):
        c = text[i]
        pair = text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                result.extend('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                result.extend('  ')
                i += 2
            else:
                result.append('\n' if c == '\n' else ' ')
                i += 1
        elif string:
            if c == '\\' and i + 1 < len(text):
                result.extend('  ')
                i += 2
            else:
                if c == '"':
                    string = False
                result.append('\n' if c == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            result.extend('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            result.extend(' ' * (end - i))
            i = end
        elif c == '"':
            string = True
            result.append(' ')
            i += 1
        else:
            result.append(c)
            i += 1
    return ''.join(result)


def imports(text):
    return [module for line in re.findall(r'^\s*import[ \t]+([^\n]+)', uncomment(text), re.M)
            for module in line.split()]


def render():
    base = ROOT / 'lean'
    paths = {str(p.relative_to(base).with_suffix('')).replace('/', '.'): p
             for p in [*base.glob('*.lean'), *base.joinpath('Yulang').rglob('*.lean')]}
    graph = {module: imports(path.read_text()) for module, path in paths.items()}

    def closure(root):
        seen = set()
        todo = [root]
        while todo:
            module = todo.pop()
            if module in seen or module not in paths:
                continue
            seen.add(module)
            todo.extend(graph[module])
        return seen

    roots = {name: closure(name) for name in ['Main', 'Audit']}
    scope = sorted(module for module in roots['Main'] | roots['Audit']
                   if module.startswith('Yulang.CommonRole'))
    mentions = set(re.findall(r'\bCommonRole[A-Za-z0-9_]+\b', LEDGER.read_text()))
    rows = ['module\tpath\tsha256\tmain_import_reachable\taudit_import_reachable\tledger_mentioned\tdirect_local_imports']
    for module in scope:
        path = paths[module]
        rows.append('\t'.join([module, str(path.relative_to(ROOT)),
                               hashlib.sha256(path.read_bytes()).hexdigest(),
                               str(int(module in roots['Main'])), str(int(module in roots['Audit'])),
                               str(int(module.split('.')[-1] in mentions)),
                               (';'.join(i for i in graph[module] if i in paths) or '-')]))
    summary = (f'CommonRole import scope={len(scope)}; Main={sum(m in roots["Main"] for m in scope)}; '
               f'Audit={sum(m in roots["Audit"] for m in scope)}; '
               f'ledger mentioned={sum(m.split(".")[-1] in mentions for m in scope)}. '
               'Mention counts are not audit completion counts.')
    return '\n'.join(rows) + '\n', summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    assert imports('/- import Hidden\n /- import Nested -/ -/\nimport Yulang.A Yulang.B -- tail\n') == ['Yulang.A', 'Yulang.B']
    assert imports('def text := "import Hidden"\nimport Yulang.C\n') == ['Yulang.C']
    expected, summary = render()
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_text() != expected:
            print('FAIL: inventory differs; regenerate after reviewing source/ledger changes.', file=sys.stderr)
            return 1
        print('PASS: inventory matches source hashes, imports, and ledger mentions.')
    else:
        OUTPUT.write_text(expected)
    print(summary)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
