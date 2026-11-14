"""Read explicit public theorem names, preserving the project's namespace scopes.

This indexes source declarations only. Acceptance still requires the Lean
environment to contain every indexed theorem and to pass the axiom audit.
"""
import re


def theorem_names(source):
    # Strip nested Lean block comments while preserving newlines.
    out, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if source[i] == '\n':
                out.append('\n')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError('Unclosed Lean comment')
    scopes, names = [], []
    for line in ''.join(out).splitlines():
        line = line.lstrip()
        m = re.match(r'^namespace\s+([\w.]+)\s*$', line)
        if m:
            scopes.append(('namespace', m[1]))
            continue
        m = re.match(r'^(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$', line)
        if m:
            scopes.append(('section', m[1] or ''))
            continue
        m = re.match(r'^end(?:\s+([\w.]+))?\s*$', line)
        if m:
            if not scopes:
                raise ValueError('Unmatched end')
            kind, name = scopes.pop()
            if m[1] and name != m[1]:
                raise ValueError(f'Scope mismatch: end {m[1]}, open {name}')
            continue
        m = re.match(r'^theorem\s+([\w.\']+)', line)
        if m:
            name = m[1]
            prefix = '.'.join(n for k, n in scopes if k == 'namespace')
            names.append(name.removeprefix('_root_.') if name.startswith('_root_.')
                         else '.'.join(x for x in [prefix, name] if x))
    return names


if __name__ == '__main__':
    example = '''/- namespace Wrong /- nested -/ -/
noncomputable section
namespace Oberwolfach
theorem first : True := trivial
namespace UniformSampleSpec
theorem mgf : True := trivial
end UniformSampleSpec
section local_setup
  theorem second : True := trivial
end local_setup
private theorem hidden : True := trivial
end Oberwolfach
'''
    assert theorem_names(example) == ['Oberwolfach.first',
        'Oberwolfach.UniformSampleSpec.mgf', 'Oberwolfach.second']
    print('Namespace indexing check passed')
