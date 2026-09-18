#!/usr/bin/env python3
"""Static source audit only. This is not a Lean parser or a kernel checker."""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def mask_noncode(text: str) -> str:
    """Mask nested Lean comments and strings while retaining offsets/newlines."""
    chars = list(text)
    i, n, depth = 0, len(text), 0
    quoted = False
    line_comment = False
    while i < n:
        if line_comment:
            if text[i] == '\n':
                line_comment = False
            else:
                chars[i] = ' '
            i += 1
        elif depth:
            if text.startswith('/-', i):
                chars[i:i + 2] = [' ', ' ']
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                chars[i:i + 2] = [' ', ' ']
                depth -= 1
                i += 2
            else:
                if text[i] != '\n':
                    chars[i] = ' '
                i += 1
        elif quoted:
            if text[i] == '\\' and i + 1 < n:
                chars[i] = ' '
                if text[i + 1] != '\n':
                    chars[i + 1] = ' '
                i += 2
            elif text[i] == '"':
                chars[i] = ' '
                quoted = False
                i += 1
            else:
                if text[i] != '\n':
                    chars[i] = ' '
                i += 1
        elif text.startswith('--', i):
            chars[i:i + 2] = [' ', ' ']
            line_comment = True
            i += 2
        elif text.startswith('/-', i):
            chars[i:i + 2] = [' ', ' ']
            depth = 1
            i += 2
        elif text[i] == '"':
            chars[i] = ' '
            quoted = True
            i += 1
        else:
            i += 1
    if depth or quoted:
        raise ValueError('Unterminated block comment or string')
    return ''.join(chars)


def audit() -> dict:
    paths = sorted((ROOT / 'SoberonConvexBody').rglob('*.lean'))
    paths += [ROOT / 'SoberonConvexBody.lean', ROOT / 'Solution.lean']
    sources = {}
    graph: dict[str, list[str]] = {}
    findings = []
    errors = []
    declarations = re.compile(
        r'(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*'
        r'(?:theorem|lemma|def|abbrev|axiom|opaque|instance|structure|class)\s+([^\s(:]+)'
    )
    forbidden = re.compile(r'\b(?:sorry|admit|axiom|sorryAx|unsafe|native_decide)\b')
    for path in paths:
        relative = path.relative_to(ROOT).as_posix()
        raw = path.read_bytes()
        text = raw.decode('utf-8')
        try:
            code = mask_noncode(text)
        except ValueError as err:
            errors.append({'file': relative, 'error': str(err)})
            code = text
        module = relative[:-5].replace('/', '.')
        local_imports = [
            name
            for name in re.findall(r'^\s*import\s+(\S+)', code, re.M)
            if name == 'SoberonConvexBody' or name.startswith('SoberonConvexBody.')
        ]
        graph[module] = local_imports
        ds = list(declarations.finditer(code))
        for hit in forbidden.finditer(code):
            prior = [d for d in ds if d.start() <= hit.start()]
            findings.append({
                'file': relative,
                'line': text.count('\n', 0, hit.start()) + 1,
                'token': hit.group(),
                'nearest_declaration': prior[-1].group(1) if prior else None,
            })
        sources[relative] = {
            'sha256': hashlib.sha256(raw).hexdigest(),
            'lines': len(text.splitlines()),
            'local_imports': local_imports,
        }
    for module, imports in graph.items():
        for dependency in imports:
            if dependency not in graph:
                errors.append({'module': module, 'missing_local_import': dependency})
    state: dict[str, int] = {}
    stack: list[str] = []
    order: list[str] = []

    def visit(module: str) -> None:
        if state.get(module) == 2:
            return
        if state.get(module) == 1:
            errors.append({'import_cycle': stack[stack.index(module):] + [module]})
            return
        state[module] = 1
        stack.append(module)
        for dependency in graph[module]:
            if dependency in graph:
                visit(dependency)
        stack.pop()
        state[module] = 2
        order.append(module)

    for module in sorted(graph):
        visit(module)
    counts = {key: sum(f['token'] == key for f in findings)
              for key in ('sorry', 'axiom', 'admit', 'sorryAx', 'unsafe', 'native_decide')}
    return {
        'audit_type': 'static text and local import graph only',
        'kernel_checked': False,
        'elaboration_checked': False,
        'counts': counts,
        'findings': findings,
        'errors': errors,
        'dependency_order': order,
        'sources': sources,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--strict', action='store_true',
                        help='Fail if proof gaps or forbidden proof mechanisms remain.')
    args = parser.parse_args()
    result = audit()
    destination = ROOT / 'validation' / 'source_audit.json'
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print('STATIC AUDIT ONLY; no Lean elaboration or kernel check has occurred.')
    print(json.dumps(result['counts'], sort_keys=True))
    for finding in result['findings']:
        print('{file}:{line}: {token} ({nearest_declaration})'.format(**finding))
    for error in result['errors']:
        print('ERROR:', error)
    print('Report:', destination.relative_to(ROOT))
    failed = bool(result['errors'] or (args.strict and result['findings']))
    return 1 if failed else 0


if __name__ == '__main__':
    raise SystemExit(main())
