#!/usr/bin/env python3
"""Generate Coq input from Octez Micheline JSON; generator is trusted.

This checks decoder examples against entire ASTs. It does not verify the JSON
parser, this generator, the Octez parser, or the interpretation of instructions.
"""
from pathlib import Path
import argparse, hashlib, json

def q(s):
    if not isinstance(s, str) or not all(32 <= ord(c) < 127 for c in s):
        raise ValueError('this importer supports ASCII scalar text only')
    return '"' + s.replace('"', '""') + '"'

def visit(x):
    if isinstance(x, list):
        children = [visit(a) for a in x]
        return [f'TSeq {len(x)}'] + sum((t for t, _ in children), []), 'MSeq [' + ';'.join(v for _, v in children) + ']'
    if not isinstance(x, dict):
        raise ValueError('expected a Micheline node')
    if 'prim' in x:
        if not set(x) <= {'prim', 'args', 'annots'}:
            raise ValueError('unexpected primitive node fields')
        args, annots = x.get('args', []), x.get('annots', [])
        if not isinstance(args, list) or not isinstance(annots, list):
            raise ValueError('primitive args and annots must be arrays')
        children = [visit(a) for a in args]
        annotations = '[' + ';'.join(q(a) for a in annots) + ']'
        return [f'TPrim {q(x["prim"])} {len(args)} {annotations}'] + sum((t for t, _ in children), []), 'MPrim ' + q(x['prim']) + ' [' + ';'.join(v for _, v in children) + '] ' + annotations
    if len(x) != 1:
        raise ValueError('expected one scalar field')
    k = next(iter(x))
    if k not in ('int', 'string', 'bytes'):
        raise ValueError('unknown scalar field')
    return [f'T{k.title()} {q(x[k])}'], f'M{k.title()} {q(x[k])}'

def render_programs(programs):
    """Accept the exact five already-parsed snapshot ASTs used by check_order."""
    names = ('fa12', 'fa2', 'ticket', 'ingress', 'egress')
    if set(programs) != set(names):
        raise ValueError('expected exactly the five pinned program ASTs')
    lines = ['From Coq Require Import List String.', 'Require Import MichelineRaw.', 'Import ListNotations.', 'Open Scope string_scope.']
    for name in names:
        ast = programs[name]
        raw = json.dumps(ast, sort_keys=True, separators=(',', ':')).encode()
        tokens, tree = visit(ast)
        lines += [f'(* Canonical JSON SHA256 {hashlib.sha256(raw).hexdigest()}; {len(tokens)} nodes. *)',
                  f'Definition {name}_tokens := [' + ';\n'.join(tokens) + '].',
                  f'Definition {name}_expected := {tree}.',
                  f'Example {name}_decoder_accepts_all_fields : decode_complete 128 {name}_tokens = Some {name}_expected.',
                  'Proof. vm_compute. reflexivity. Qed.']
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--input-dir', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    programs = {name: json.loads((args.input_dir / f'{name}.micheline.json').read_bytes())
                for name in ('fa12', 'fa2', 'ticket', 'ingress', 'egress')}
    args.output.write_text(render_programs(programs))
