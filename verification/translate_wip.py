"""Partial syntax-directed Michelson-to-WIP VM translation; NOT proved sound.

Unsupported nodes are preserved verbatim, encoded as hex JSON, in an opaque
Prim constructor. A proof assuming arbitrary Prim behavior is not a proof of
Octez. Control-flow bodies of supported combinators are translated recursively.
"""
import collections
import json

def translate_program(code, overrides=None):
    opaque = collections.Counter()
    overrides = overrides or {}
    def seq(nodes):
        return '[' + '; '.join(node(n) for n in nodes) + ']'
    def node(n):
        p, a = n['prim'], n.get('args', [])
        if p in overrides:
            expected, result = overrides[p]
            if n != expected: raise ValueError(f'unexpected overridden instruction shape {p}: {n}')
            return result
        simple = {'SWAP': 'Swap', 'NIL': 'Nil', 'CONS': 'Cons', 'ADD': 'Add',
                  'SUB': 'Sub', 'ABS': 'Abs', 'EQ': 'IsEq', 'GT': 'IsGt',
                  'LT': 'IsLt', 'FAILWITH': 'Fail', 'UNIT': 'Unit', 'SOME': 'SomeValue',
                  'NONE': 'NoneValue', 'CAR': 'Car', 'CDR': 'Cdr', 'READ_TICKET': 'ReadTicket', 'SIZE': 'Size',
                  'INT': 'ToInt', 'ISNAT': 'IsNat'}
        if p in simple and (not a or p in ('NIL', 'NONE')):
            return 'FullVM_WIP.' + simple[p]
        if p == 'DROP' and not a: return 'FullVM_WIP.Drop'
        if p == 'DROP' and len(a) == 1: return 'FullVM_WIP.DropN ' + a[0]['int']
        if p == 'PUSH' and len(a) == 2 and a[0].get('prim') == 'nat' and 'int' in a[1]:
            return 'FullVM_WIP.Push (FullVM_WIP.VNat ' + a[1]['int'] + ')'
        if p == 'PUSH' and len(a) == 2 and a[0].get('prim') == 'int' and 'int' in a[1]:
            return 'FullVM_WIP.Push (FullVM_WIP.VInt (' + a[1]['int'] + ')%Z)'
        if p == 'PUSH' and len(a) == 2 and a[0].get('prim') == 'mutez' and 'int' in a[1]:
            return 'FullVM_WIP.Push (FullVM_WIP.VMutez ' + a[1]['int'] + ')'
        if p == 'PUSH' and len(a) == 2 and a[0] == {'prim': 'bool'} and a[1] in ({'prim': 'True'}, {'prim': 'False'}):
            return 'FullVM_WIP.Push (FullVM_WIP.VBool ' + ('true' if a[1]['prim'] == 'True' else 'false') + ')'
        if p == 'PUSH' and len(a) == 2 and a[0].get('prim') == 'string' and 'string' in a[1]:
            return 'FullVM_WIP.Push (FullVM_WIP.VString [' + '; '.join(str(b) + '%nat' for b in a[1]['string'].encode()) + '])'
        if p == 'EMPTY_MAP': return 'FullVM_WIP.EmptyMap'
        if p in ('PAIR', 'UNPAIR') and not a:
            return 'FullVM_WIP.' + ('Pair' if p == 'PAIR' else 'Unpair')
        if p in ('PAIR', 'UNPAIR') and len(a) == 1 and 'int' in a[0]:
            return 'FullVM_WIP.' + ('PairN ' if p == 'PAIR' else 'UnpairN ') + a[0]['int']
        if p in ('DUP', 'DIG', 'DUG'):
            nvalue = int(a[0]['int']) if a else 1
            return 'FullVM_WIP.' + {'DUP': 'Dup', 'DIG': 'Dig', 'DUG': 'Dug'}[p] + ' ' + str(nvalue)
        if p in ('IF', 'IF_NONE'):
            return 'FullVM_WIP.' + ('If' if p == 'IF' else 'IfNone') + ' ' + seq(a[0]) + ' ' + seq(a[1])
        if p == 'DIP':
            depth, body = (int(a[0]['int']), a[1]) if len(a) == 2 else (1, a[0])
            return 'FullVM_WIP.Dip ' + str(depth) + ' ' + seq(body)
        if p in ('ITER', 'MAP'):
            return 'FullVM_WIP.' + ('Iter' if p == 'ITER' else 'Map') + ' ' + seq(a[0])
        opaque[p] += 1
        encoded = json.dumps(n, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode().hex()
        return 'FullVM_WIP.Prim "jsonhex:' + encoded + '"'
    return seq(code), opaque
