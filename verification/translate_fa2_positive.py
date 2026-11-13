"""Extract the positive FA2 ITER path into the partial Coq VM.

The nonpositive branch is intentionally replaced by an opaque marker. This is
not a whole-body translation or a proved semantics-preserving compiler.
"""
from translate_wip import translate_program

def translate_positive(code):
    loops = [n for n in code if n.get('prim') == 'ITER']
    if len(loops) != 1: raise ValueError('expected exactly one top-level FA2 ITER')
    body = loops[0]['args'][0]
    fail = [{'prim': 'UNIT'}, {'prim': 'FAILWITH'}]
    expected = [
        {'prim': 'SAPLING_VERIFY_UPDATE'}, {'prim': 'IF_NONE', 'args': [fail, []]},
        {'prim': 'UNPAIR', 'args': [{'int': '3'}]}, {'prim': 'DUG', 'args': [{'int': '2'}]},
        {'prim': 'DUP'}, {'prim': 'DUP'}, {'prim': 'ABS'}, {'prim': 'DUG', 'args': [{'int': '2'}]}, {'prim': 'GT'}]
    if len(body) != 10 or body[:9] != expected or body[9].get('prim') != 'IF':
        raise ValueError('FA2 Sapling loop prefix shape changed')
    positive = body[9]['args'][0]
    overrides = {
        'SAPLING_VERIFY_UPDATE': ({'prim': 'SAPLING_VERIFY_UPDATE'}, 'FullVM_WIP.Prim "SAPLING_VERIFY_UPDATE"'),
        'UNPACK': ({'prim': 'UNPACK', 'args': [{'prim': 'address'}]}, 'FullVM_WIP.Prim "UNPACK_address"'),
        'PACK': ({'prim': 'PACK'}, 'FullVM_WIP.Prim "PACK_address"'),
        # Only this type-checked local SIZE/PUSH-nat comparison is specialized.
        'COMPARE': ({'prim': 'COMPARE'}, 'FullVM_WIP.CompareInt'),
    }
    head, opaque_head = translate_program(body[:9], overrides)
    yes, opaque_yes = translate_program(positive, overrides)
    if opaque_head or opaque_yes:
        raise ValueError(f'unsupported FA2 positive path instructions: {opaque_head}, {opaque_yes}')
    return head[:-1] + '; FullVM_WIP.If ' + yes + ' [FullVM_WIP.Prim "NONPOSITIVE_BRANCH_NOT_MODELED"]]'
