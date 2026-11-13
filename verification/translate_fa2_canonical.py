"""Translate the exact FA2 loop into the shared partial VM.

The full script remains type-erased; correctness of this translation and of
named callbacks relative to Octez is trusted. This translation is restricted
to the pinned FA2 loop where COMPARE is used on modeled naturals.
"""
from translate_wip import translate_program

def translate_canonical_body(loop_body):
    overrides = {
        'SAPLING_VERIFY_UPDATE': ({'prim': 'SAPLING_VERIFY_UPDATE'}, 'FullVM_WIP.Prim "SAPLING_VERIFY_UPDATE"'),
        'UNPACK': ({'prim': 'UNPACK', 'args': [{'prim': 'address'}]}, 'FullVM_WIP.Prim "UNPACK_address"'),
        'PACK': ({'prim': 'PACK'}, 'FullVM_WIP.Prim "PACK_address"'),
        'COMPARE': ({'prim': 'COMPARE'}, 'FullVM_WIP.CompareInt'),
        'SENDER': ({'prim': 'SENDER'}, 'FullVM_WIP.Prim "SENDER"'),
        'GET': ({'prim': 'GET'}, 'FullVM_WIP.Prim "GET"'),
        'UPDATE': ({'prim': 'UPDATE'}, 'FullVM_WIP.Prim "UPDATE"'),
    }
    program, opaque = translate_program(loop_body, overrides)
    if opaque:
        raise ValueError(f'unsupported canonical FA2 loop nodes: {opaque}')
    return program
