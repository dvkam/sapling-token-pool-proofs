#!/usr/bin/env python3
"""Pin and parse real FA2 source, then check fragment theorems in Coq.

The parser, selection of the containing branch, and Michelson-to-Coq fragment
translation are trusted. This is NOT a proof of whole-contract behavior.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from translate_wip import translate_program
from translate_micheline_raw import render_programs
from translate_fa2_positive import translate_positive
from translate_fa2_canonical import translate_canonical_body

HERE = Path(__file__).resolve().parent
PIN = '4527dbc0bfcbbb795a099349ee1207ea65a9a98ca83e10331b82946f04535163'
FA12_PIN = 'ac29f6ddc86e055eeee8fe7e1aacbf58216cc68090952c3c4fa065924f08ebf1'
TICKET_PIN = 'efa68bf8c66c12c65008cbf5871d494574c3a7a21ebb450c653b2fc6734ee5cb'
INGRESS_PIN = '22eef9d75bd6b8e0f9f934f6c8737d4c7c717a81d98dd64a363529b1ca7e1d9a'
EGRESS_PIN = '0a102ec7e76fdf0b4bf083e019b2173f7d6933ad4600e29155b83fe905762281'

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--contract', type=Path, required=True)
parser.add_argument('--ticket-contract', type=Path, default=HERE.parent / 'contracts/sapling_contract_tickets.tz')
parser.add_argument('--fa12-contract', type=Path, default=HERE.parent / 'contracts/sapling_contract_fa_1_2.tz')
parser.add_argument('--adapter-ingress', type=Path, default=HERE.parent / 'contracts/sapling_fa21_ingress.tz')
parser.add_argument('--adapter-egress', type=Path, default=HERE.parent / 'contracts/sapling_fa21_egress.tz')
parser.add_argument('--expected-ingress-sha256', default=INGRESS_PIN, help='Override only for reviewed deliberate source mutations')
parser.add_argument('--expected-egress-sha256', default=EGRESS_PIN, help='Override only for reviewed deliberate source mutations')
parser.add_argument('--client', required=True)
parser.add_argument('--base-dir', type=Path, required=True)
parser.add_argument('--coqc', default='coqc')
parser.add_argument('--coqchk', default='coqchk')
parser.add_argument('--artifacts-dir', type=Path, default=HERE.parent / '.local/verification',
                    help='Parent for a new uniquely named proof-artifact directory')
parser.add_argument('--expected-sha256', default=PIN,
                    help='Override only for reviewed deliberate source mutations')
parser.add_argument('--expected-ticket-sha256', default=TICKET_PIN,
                    help='Override only for reviewed deliberate ticket source mutations')
parser.add_argument('--expected-fa12-sha256', default=FA12_PIN,
                    help='Override only for reviewed deliberate FA1.2 source mutations')
args = parser.parse_args()
def binary_hash(binary):
    resolved = shutil.which(binary) or binary
    with open(resolved, 'rb') as handle: return hashlib.file_digest(handle, 'sha256').hexdigest()
tool_hashes = {'octez_client': binary_hash(args.client), 'coqc': binary_hash(args.coqc), 'coqchk': binary_hash(args.coqchk)}
proof_inputs = sorted([*HERE.glob('*.v'), *HERE.glob('*.py')])
proof_input_hashes = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in proof_inputs}

original_paths = {'fa2': args.contract.resolve(), 'fa12': args.fa12_contract.resolve(),
                  'ticket': args.ticket_contract.resolve(), 'ingress': args.adapter_ingress.resolve(), 'egress': args.adapter_egress.resolve()}
original_bytes = {key: path.read_bytes() for key, path in original_paths.items()}
snapshot = tempfile.TemporaryDirectory(prefix='sapling-source-snapshot-')
snapshot_paths = {key: Path(snapshot.name) / (key + '.tz') for key in original_paths}
for key, path in snapshot_paths.items(): path.write_bytes(original_bytes[key])
args.contract, args.fa12_contract, args.ticket_contract = snapshot_paths['fa2'], snapshot_paths['fa12'], snapshot_paths['ticket']
args.adapter_ingress, args.adapter_egress = snapshot_paths['ingress'], snapshot_paths['egress']
source = original_bytes['fa2']
digest = hashlib.sha256(source).hexdigest()
if digest != args.expected_sha256:
    raise SystemExit(f'FA2 source hash changed: {digest}; review before updating the pin')

common = [args.client, '--base-dir', str(args.base_dir), '--mode', 'mockup']
subprocess.run(common + ['typecheck', 'script', str(args.contract)], check=True, capture_output=True)
data = json.loads(subprocess.run(common + ['convert', 'script', str(args.contract), 'from', 'michelson', 'to', 'json'],
                                 check=True, capture_output=True, text=True).stdout)
code = next(x['args'][0] for x in data if x.get('prim') == 'code')
adapter_data = {}
adapter_digest = {}
for label, path, expected in (
    ('ingress', args.adapter_ingress, args.expected_ingress_sha256),
    ('egress', args.adapter_egress, args.expected_egress_sha256),
):
    adapter_digest[label] = hashlib.sha256(original_bytes[label]).hexdigest()
    if adapter_digest[label] != expected:
        raise SystemExit(f'{label} adapter source hash changed: {adapter_digest[label]}; review before updating the pin')
    subprocess.run(common + ['typecheck', 'script', str(path)], check=True, capture_output=True)
    adapter_data[label] = json.loads(subprocess.run(
        common + ['convert', 'script', str(path), 'from', 'michelson', 'to', 'json'],
        check=True, capture_output=True, text=True).stdout)
adapter_code = {label: next(x['args'][0] for x in ast if x.get('prim') == 'code')
                for label, ast in adapter_data.items()}
ingress, egress = adapter_code['ingress'], adapter_code['egress']
if len(ingress) != 43 or ingress[24] != {'prim': 'DROP'}:
    raise SystemExit('Adapter ingress post-guard source shape changed')
if len(egress) != 51 or egress[28] != {'prim': 'DROP'}:
    raise SystemExit('Adapter egress post-guard source shape changed')
if egress[29] != {'prim': 'DUP', 'args': [{'int': '4'}]}:
    raise SystemExit('Adapter egress beneficiary selector changed')
try:
    ingress_used = ingress[38]['args'][0][0]['args'][1][1]
except (KeyError, IndexError, TypeError) as exc:
    raise SystemExit('Adapter ingress one-shot flag structure changed') from exc
if ingress_used != {'prim': 'PUSH', 'args': [{'prim': 'bool'}, {'prim': 'True'}]}:
    raise SystemExit('Adapter ingress one-shot flag changed')
ticket_payload = {'prim': 'pair', 'args': [{'prim': 'nat'}, {'prim': 'option', 'args': [{'prim': 'bytes'}]}]}
ticket_type = {'prim': 'ticket', 'args': [ticket_payload]}
pool_contract_node = {'prim': 'CONTRACT', 'args': [{'prim': 'pair', 'args': [
    {'prim': 'option', 'args': [ticket_type]},
    {'prim': 'list', 'args': [{'prim': 'sapling_transaction', 'args': [{'int': '8'}]}]}]}]}
import_contract_node = {'prim': 'CONTRACT', 'annots': ['%import_ticket'], 'args': [
    {'prim': 'list', 'args': [{'prim': 'pair', 'args': [
        {'prim': 'address'}, {'prim': 'list', 'args': [ticket_type]}]}]}]}
if ingress[33] != pool_contract_node or egress[41] != import_contract_node:
    raise SystemExit('Adapter typed pool/import contract lookup changed')
if ingress[34].get('prim') != 'IF_NONE' or egress[42].get('prim') != 'IF_NONE':
    raise SystemExit('Adapter contract lookup failure branch changed')
def translate_adapter(nodes, contract_node, name):
    program, opaque = translate_program(nodes, {
        'CONTRACT': (contract_node, f'FullVM_WIP.Prim "{name}"'),
        'TRANSFER_TOKENS': ({'prim': 'TRANSFER_TOKENS'}, 'FullVM_WIP.Prim "TRANSFER_TOKENS"'),
    })
    if opaque: raise ValueError(f'unsupported adapter route nodes: {opaque}')
    return program
ingress_route_program = translate_adapter(ingress[25:], pool_contract_node, 'CONTRACT_pool')
egress_route_program = translate_adapter(egress[29:], import_contract_node, 'CONTRACT_import')
ingress_reject_program = translate_adapter(ingress[34]['args'][0], pool_contract_node, 'CONTRACT_pool')
egress_reject_program = translate_adapter(egress[42]['args'][0], import_contract_node, 'CONTRACT_import')
def translate_adapter_full(nodes, split, contract_node, name):
    common_adapter = {
        'AMOUNT': ({'prim': 'AMOUNT'}, 'FullVM_WIP.Prim "AMOUNT"'),
        'SENDER': ({'prim': 'SENDER'}, 'FullVM_WIP.Prim "SENDER"'),
        'PACK': ({'prim': 'PACK'}, 'FullVM_WIP.Prim "PACK_address"'),
        'CONTRACT': (contract_node, f'FullVM_WIP.Prim "{name}"'),
        'TRANSFER_TOKENS': ({'prim': 'TRANSFER_TOKENS'}, 'FullVM_WIP.Prim "TRANSFER_TOKENS"'),
    }
    prefix = dict(common_adapter, COMPARE=({'prim': 'COMPARE'}, 'FullVM_WIP.CompareInt'))
    suffix = dict(common_adapter, COMPARE=({'prim': 'COMPARE'}, 'FullVM_WIP.Prim "COMPARE_value"'))
    a, ao = translate_program(nodes[:split], prefix)
    b, bo = translate_program(nodes[split:], suffix)
    if ao or bo: raise ValueError(f'unsupported complete adapter nodes: {ao}, {bo}')
    return a + ' ++ ' + b
ingress_full_program = translate_adapter_full(ingress, 5, pool_contract_node, 'CONTRACT_pool')
egress_full_program = translate_adapter_full(egress, 14, import_contract_node, 'CONTRACT_import')


if code[-1].get('prim') != 'IF':
    raise SystemExit('Source shape changed: expected final operation branch')
branch = code[-1]['args'][1]
def is_reverse_at(i):
    return (branch[i].get('prim') == 'NIL' and branch[i + 1] == {'prim': 'SWAP'}
            and branch[i + 2] == {'prim': 'ITER', 'args': [[{'prim': 'CONS'}]]})
if (len(branch) != 24 or not is_reverse_at(7) or not is_reverse_at(14)
        or branch[6] != {'prim': 'DIG', 'args': [{'int': '3'}]}
        or branch[10].get('prim') != 'MAP'
        or branch[11:14] != [{'prim': 'SELF_ADDRESS'}, {'prim': 'PAIR'}, {'prim': 'CONS'}]
        or branch[17:20] != [{'prim': 'PUSH', 'args': [{'prim': 'mutez'}, {'int': '0'}]},
                            {'prim': 'SWAP'}, {'prim': 'TRANSFER_TOKENS'}]):
    raise SystemExit('Source shape changed: expected both reversal fragments and operation context')
loops = [n for n in code if n.get('prim') == 'ITER']
if len(loops) != 1:
    raise SystemExit('FA2 transaction loop shape changed')
loop_body = loops[0]['args'][0]
nonpositive_expected = [
    {'prim': 'DIG', 'args': [{'int': '3'}]}, {'prim': 'SIZE'},
    {'prim': 'PUSH', 'args': [{'prim': 'nat'}, {'int': '0'}]}, {'prim': 'COMPARE'},
    {'prim': 'EQ'}, {'prim': 'IF', 'args': [[], [{'prim': 'UNIT'}, {'prim': 'FAILWITH'}]]}]
if len(loop_body) != 10 or loop_body[9].get('prim') != 'IF' or loop_body[9]['args'][1][:6] != nonpositive_expected:
    raise SystemExit('FA2 nonpositive bound-data guard shape changed')
nonpositive_program, opaque = translate_program(nonpositive_expected, {
    'COMPARE': ({'prim': 'COMPARE'}, 'FullVM_WIP.CompareInt')})
if opaque: raise SystemExit(f'Unexpected opaque instruction in nonpositive guard: {opaque}')
loop_program = translate_canonical_body(loop_body)
boundary_overrides = {
    'AMOUNT': ({'prim': 'AMOUNT'}, 'FullVM_WIP.Prim "AMOUNT"'),
    'SELF_ADDRESS': ({'prim': 'SELF_ADDRESS'}, 'FullVM_WIP.Prim "SELF_ADDRESS"'),
    'COMPARE': ({'prim': 'COMPARE'}, 'FullVM_WIP.CompareInt'),
}
def translate_boundary(nodes):
    result, opaque = translate_program(nodes, boundary_overrides)
    if opaque:
        raise ValueError(f'unsupported FA2 boundary nodes: {opaque}')
    return result
if len(code) != 20 or code[19].get('prim') != 'IF' or len(code[19].get('args', [])) != 2:
    raise ValueError('FA2 boundary control-flow shape changed')
boundary_guard = translate_boundary(code[:5])
boundary_init = translate_boundary(code[5:10])
private_prefix = translate_boundary(code[11:19])
private_arm = translate_boundary(code[19]['args'][0])
public_arm = code[19]['args'][1]
if len(public_arm) != 24 or public_arm[5].get('prim') != 'ITER':
    raise ValueError('FA2 public deposit iteration shape changed')
deposit_group_body = translate_boundary(public_arm[5]['args'][0])
if public_arm[10].get('prim') != 'MAP':
    raise ValueError('FA2 public withdrawal mapping shape changed')
withdrawal_item_body = translate_boundary(public_arm[10]['args'][0])
fa2_contract_node = {'prim': 'CONTRACT', 'annots': ['%transfer'], 'args': [
    {'prim': 'list', 'args': [{'prim': 'pair', 'args': [
        {'prim': 'address'}, {'prim': 'list', 'args': [{'prim': 'pair', 'args': [
            {'prim': 'address'}, {'prim': 'nat'}, {'prim': 'nat'}]}]}]}]}]}
if public_arm[1] != fa2_contract_node:
    raise ValueError('FA2 transfer contract type or entrypoint changed')
fa2_full_overrides = dict(boundary_overrides)
fa2_full_overrides.update({
    'SAPLING_VERIFY_UPDATE': ({'prim': 'SAPLING_VERIFY_UPDATE'}, 'FullVM_WIP.Prim "SAPLING_VERIFY_UPDATE"'),
    'UNPACK': ({'prim': 'UNPACK', 'args': [{'prim': 'address'}]}, 'FullVM_WIP.Prim "UNPACK_address"'),
    'PACK': ({'prim': 'PACK'}, 'FullVM_WIP.Prim "PACK_address"'),
    'SENDER': ({'prim': 'SENDER'}, 'FullVM_WIP.Prim "SENDER"'),
    'GET': ({'prim': 'GET'}, 'FullVM_WIP.Prim "GET"'),
    'UPDATE': ({'prim': 'UPDATE'}, 'FullVM_WIP.Prim "UPDATE"'),
    'CONTRACT': (fa2_contract_node, 'FullVM_WIP.Prim "CONTRACT_FA2_TRANSFER"'),
    'TRANSFER_TOKENS': ({'prim': 'TRANSFER_TOKENS'}, 'FullVM_WIP.Prim "TRANSFER_TOKENS"'),
})
fa2_full_program, fa2_full_opaque = translate_program(code, fa2_full_overrides)
fa2_public_program, fa2_public_opaque = translate_program(public_arm, fa2_full_overrides)
if fa2_full_opaque or fa2_public_opaque:
    raise ValueError(f'unsupported FA2 full program nodes: {fa2_full_opaque}, {fa2_public_opaque}')




fa12_digest = hashlib.sha256(args.fa12_contract.read_bytes()).hexdigest()
if fa12_digest != args.expected_fa12_sha256:
    raise SystemExit(f'FA1.2 source hash changed: {fa12_digest}; review before updating the pin')
subprocess.run(common + ['typecheck', 'script', str(args.fa12_contract)], check=True, capture_output=True)
fa12_data = json.loads(subprocess.run(common + ['convert', 'script', str(args.fa12_contract), 'from', 'michelson', 'to', 'json'],
                                      check=True, capture_output=True, text=True).stdout)
fa12_code = next(x['args'][0] for x in fa12_data if x.get('prim') == 'code')
fa12_tail = [
    {'prim': 'SWAP'}, {'prim': 'DROP'}, {'prim': 'DIG', 'args': [{'int': '2'}]}, {'prim': 'UNPAIR'},
    {'prim': 'DIP', 'args': [[{'prim': 'NIL', 'args': [{'prim': 'operation'}]}, {'prim': 'SWAP'},
                             {'prim': 'ITER', 'args': [[{'prim': 'CONS'}]]}]]},
    {'prim': 'ITER', 'args': [[{'prim': 'CONS'}]]}, {'prim': 'PAIR', 'args': [{'int': '3'}]}]
if fa12_code[-7:] != fa12_tail:
    raise SystemExit('FA1.2 final order fragment shape changed')

ticket_digest = hashlib.sha256(args.ticket_contract.read_bytes()).hexdigest()
if ticket_digest != args.expected_ticket_sha256:
    raise SystemExit(f'Ticket source hash changed: {ticket_digest}; review before updating the pin')
subprocess.run(common + ['typecheck', 'script', str(args.ticket_contract)], check=True, capture_output=True)
ticket_data = json.loads(subprocess.run(common + ['convert', 'script', str(args.ticket_contract), 'from', 'michelson', 'to', 'json'],
                                        check=True, capture_output=True, text=True).stdout)
ticket_code = next(x['args'][0] for x in ticket_data if x.get('prim') == 'code')
if fa12_code[11].get('prim') != 'ITER' or ticket_code[12].get('prim') != 'ITER':
    raise ValueError('FA1.2 or ticket transaction loop shape changed')
fa12_loop_nodes = fa12_code[11]['args'][0]
ticket_loop_nodes = ticket_code[12]['args'][0]
if len(ticket_loop_nodes) != 9 or ticket_loop_nodes[8].get('prim') != 'IF':
    raise ValueError('Ticket positive withdrawal branch shape changed')
ticket_withdrawal_nodes = ticket_loop_nodes[8]['args'][0]
fa12_overrides = {
    'AMOUNT': ({'prim': 'AMOUNT'}, 'FullVM_WIP.Prim "AMOUNT"'),
    'CONTRACT': ({'prim': 'CONTRACT', 'annots': ['%transfer'], 'args': [{'prim': 'pair', 'args': [{'prim': 'address'}, {'prim': 'address'}, {'prim': 'nat'}]}]}, 'FullVM_WIP.Prim "CONTRACT_FA12_TRANSFER"'),
    'SAPLING_VERIFY_UPDATE': ({'prim': 'SAPLING_VERIFY_UPDATE'}, 'FullVM_WIP.Prim "SAPLING_VERIFY_UPDATE"'),
    'UNPACK': ({'prim': 'UNPACK', 'args': [{'prim': 'address'}]}, 'FullVM_WIP.Prim "UNPACK_address"'),
    'PACK': ({'prim': 'PACK'}, 'FullVM_WIP.Prim "PACK_address"'),
    'COMPARE': ({'prim': 'COMPARE'}, 'FullVM_WIP.CompareInt'),
    'SELF_ADDRESS': ({'prim': 'SELF_ADDRESS'}, 'FullVM_WIP.Prim "SELF_ADDRESS"'),
    'SENDER': ({'prim': 'SENDER'}, 'FullVM_WIP.Prim "SENDER"'),
    'TRANSFER_TOKENS': ({'prim': 'TRANSFER_TOKENS'}, 'FullVM_WIP.Prim "TRANSFER_TOKENS"'),
}
ticket_overrides = {
    'SAPLING_VERIFY_UPDATE': ({'prim': 'SAPLING_VERIFY_UPDATE'}, 'FullVM_WIP.Prim "SAPLING_VERIFY_UPDATE"'),
    'COMPARE': ({'prim': 'COMPARE'}, 'FullVM_WIP.CompareInt'),
    'UNPACK': ({'prim': 'UNPACK', 'args': [{'prim': 'address'}]}, 'FullVM_WIP.Prim "UNPACK_address"'),
    'CONTRACT': ({'prim': 'CONTRACT', 'args': [{'prim': 'ticket', 'args': [{'prim': 'pair', 'args': [{'prim': 'nat'}, {'prim': 'option', 'args': [{'prim': 'bytes'}]}]}]}]}, 'FullVM_WIP.Prim "CONTRACT_ticket"'),
    'SPLIT_TICKET': ({'prim': 'SPLIT_TICKET'}, 'FullVM_WIP.Prim "SPLIT_ticket"'),
    'TRANSFER_TOKENS': ({'prim': 'TRANSFER_TOKENS'}, 'FullVM_WIP.Prim "TRANSFER_ticket"'),
}
fa12_loop_program, fa12_opaque = translate_program(fa12_loop_nodes, fa12_overrides)
fa12_full_program, fa12_full_opaque = translate_program(fa12_code, fa12_overrides)
ticket_withdrawal_program, ticket_opaque = translate_program(ticket_withdrawal_nodes, ticket_overrides)
ticket_loop_program, ticket_loop_opaque = translate_program(ticket_loop_nodes, ticket_overrides)
if len(ticket_code) != 23:
    raise ValueError('Ticket final-output program shape changed')
ticket_final_program, ticket_final_opaque = translate_program(ticket_code[13:], ticket_overrides)
ticket_init_prefix_overrides = dict(ticket_overrides)
ticket_init_prefix_overrides['AMOUNT'] = ({'prim': 'AMOUNT'}, 'FullVM_WIP.Prim "AMOUNT"')
ticket_init_nested_overrides = dict(ticket_init_prefix_overrides)
ticket_init_nested_overrides['COMPARE'] = ({'prim': 'COMPARE'}, 'FullVM_WIP.Prim "COMPARE_identity"')
ticket_init_nested_overrides['JOIN_TICKETS'] = ({'prim': 'JOIN_TICKETS'}, 'FullVM_WIP.Prim "JOIN_ticket"')
ticket_init_prefix, ticket_init_prefix_opaque = translate_program(ticket_code[:9], ticket_init_prefix_overrides)
ticket_init_nested, ticket_init_nested_opaque = translate_program(ticket_code[9:12], ticket_init_nested_overrides)
if ticket_init_prefix_opaque or ticket_init_nested_opaque:
    raise ValueError(f'unsupported ticket initialization nodes: {ticket_init_prefix_opaque}, {ticket_init_nested_opaque}')


if fa12_opaque or fa12_full_opaque or ticket_opaque or ticket_loop_opaque or ticket_final_opaque:
    raise ValueError(f'unsupported FA1.2/ticket branch nodes: {fa12_opaque}, {fa12_full_opaque}, {ticket_opaque}, {ticket_loop_opaque}, {ticket_final_opaque}')

try:
    stored = ticket_code[9]['args'][1][0]['args'][1]
    paid = ticket_code[10]['args'][1]
except (KeyError, IndexError, TypeError) as exc:
    raise SystemExit('Ticket identity branch shape changed') from exc
prefix = [{'prim': 'READ_TICKET'}, {'prim': 'DUP'}, {'prim': 'CAR'},
          {'prim': 'DIP', 'args': [[{'prim': 'DUP'}, {'prim': 'CDR'}, {'prim': 'CAR'}]]},
          {'prim': 'PAIR'}]
identity_guard = [{'prim': 'COMPARE'}, {'prim': 'EQ'},
                  {'prim': 'IF', 'args': [[], [{'prim': 'UNIT'}, {'prim': 'FAILWITH'}]]}]
for instructions, depth in ((stored, 4), (paid, 7)):
    if instructions[:5] != prefix or instructions[5] != {'prim': 'DUP', 'args': [{'int': str(depth)}]} or instructions[6:9] != identity_guard:
        raise SystemExit('Ticket identity guard shape changed')

coq = '''From Coq Require Import List String ZArith.\nImport ListNotations.\nRequire Import FullVM_WIP FA2Nonpositive FA2LoopBody FA2DepositBody FA2Combined FA2Environment LoopInduction FA2MixedBatch FA2Boundary FA2PrivateSuccess FA2Operations FA2Map FA2MapFuel FA2DepositFuel FA2PublicSuccess FA2SenderMap FA12LoopBody FA12MixedBatch FA12Boundary TicketWithdrawal TicketLoopBody TicketMixedBatch TicketFinal TicketPostBatch TicketInit TicketCompleteSuccess AdapterRoute AdapterAuthorization.\nOpen Scope list_scope.\n'''
coq += 'Definition parsed_vm_reverse := [FullVM_WIP.Nil; FullVM_WIP.Swap; FullVM_WIP.Iter [FullVM_WIP.Cons]].\n'
coq += f'Definition parsed_nonpositive_guard := {nonpositive_program}.\n'
coq += f'Definition parsed_fa2_positive := {translate_positive(code)}.\n'
coq += f'Definition parsed_fa2_loop_body := {loop_program}.\n'
coq += f'Definition parsed_fa2_full := {fa2_full_program}.\n'
coq += f'Definition parsed_fa2_public := {fa2_public_program}.\n'
coq += f'Definition parsed_fa2_guard := {boundary_guard}.\n'
coq += f'Definition parsed_fa12_iteration := {fa12_loop_program}.\n'
coq += f'Definition parsed_fa12_full := {fa12_full_program}.\n'
coq += f'Definition parsed_ticket_withdrawal := {ticket_withdrawal_program}.\n'
coq += f'Definition parsed_ticket_iteration := {ticket_loop_program}.\n'
coq += f'Definition parsed_ticket_init := {ticket_init_prefix} ++ {ticket_init_nested}.\n'
coq += f'Definition parsed_ingress_route := {ingress_route_program}.\n'
coq += f'Definition parsed_ingress_full := {ingress_full_program}.\n'
coq += f'Definition parsed_egress_full := {egress_full_program}.\n'
coq += f'Definition parsed_egress_route := {egress_route_program}.\n'
coq += f'Definition parsed_ingress_reject := {ingress_reject_program}.\n'
coq += f'Definition parsed_egress_reject := {egress_reject_program}.\n'

coq += f'Definition parsed_ticket_final := {ticket_final_program}.\n'
coq += f'Definition parsed_deposit_group_body := {deposit_group_body}.\n'
coq += f'Definition parsed_withdrawal_item_body := {withdrawal_item_body}.\n'
coq += f'Definition parsed_fa2_init := {boundary_init}.\n'
coq += f'Definition parsed_fa2_private_post (nonprivate : list FullVM_WIP.instruction) := {private_prefix} ++ [FullVM_WIP.If {private_arm} nonprivate].\n'

coq += '''Theorem parsed_vm_reverse_unbounded : forall (primitive : String.string -> FullVM_WIP.stack -> option FullVM_WIP.stack) xs rest,
  FullVM_WIP.run primitive 8 parsed_vm_reverse (FullVM_WIP.VList xs :: rest) =
    Some (FullVM_WIP.VList (rev xs) :: rest).
Proof. intros; apply FullVM_WIP.source_reverse_fixed_fuel. Qed.
Example nonpositive_guard_matches : parsed_nonpositive_guard = FA2Nonpositive.bound_data_check.
Proof. reflexivity. Qed.
Theorem parsed_nonpositive_empty : forall (primitive : String.string -> FullVM_WIP.stack -> option FullVM_WIP.stack) a b c rest,
  FullVM_WIP.run primitive 20 parsed_nonpositive_guard (a :: b :: c :: FullVM_WIP.VBytes [] :: rest) =
    Some (a :: b :: c :: rest).
Proof. intros; rewrite nonpositive_guard_matches; apply FA2Nonpositive.empty_bound_data_passes. Qed.
Theorem parsed_nonpositive_nonempty : forall (primitive : String.string -> FullVM_WIP.stack -> option FullVM_WIP.stack) a b c byte bytes rest,
  FullVM_WIP.run primitive 20 parsed_nonpositive_guard (a :: b :: c :: FullVM_WIP.VBytes (byte :: bytes) :: rest) = None.
Proof. intros; rewrite nonpositive_guard_matches; apply FA2Nonpositive.nonempty_bound_data_fails. Qed.
Example fa2_withdrawal_item_body_matches : parsed_withdrawal_item_body = FA2Operations.withdrawal_item_body.
Proof. reflexivity. Qed.
Theorem parsed_unbounded_withdrawal_mapping :
  forall prim entries groups handle state token token_id frame,
  FullVM_WIP.run prim 10 [FullVM_WIP.Map parsed_withdrawal_item_body]
    (FullVM_WIP.VList (List.map (fun entry => FullVM_WIP.VPair (fst entry) (snd entry)) entries) ::
     groups :: handle :: state :: token :: token_id :: frame) =
  Some (FullVM_WIP.VList (List.map (fun entry => FullVM_WIP.VPair (fst entry) (FullVM_WIP.VPair token_id (snd entry))) entries) ::
        groups :: handle :: state :: token :: token_id :: frame).
Proof. intros; rewrite fa2_withdrawal_item_body_matches; apply FA2Map.unbounded_withdrawal_mapping. Qed.
Print Assumptions parsed_unbounded_withdrawal_mapping.
Example fa2_deposit_group_body_matches : parsed_deposit_group_body = FA2Operations.deposit_group_body.
Proof. reflexivity. Qed.
Example fa12_full_matches : parsed_fa12_full = FA12Boundary.full_code.
Proof. reflexivity. Qed.
Theorem parsed_fa12_full_same : forall primitive input fuel,
  FullVM_WIP.run primitive fuel parsed_fa12_full input =
  FullVM_WIP.run primitive fuel FA12Boundary.full_code input.
Proof. intros; rewrite fa12_full_matches; reflexivity. Qed.
Example fa12_iteration_matches : parsed_fa12_iteration = FA12LoopBody.iteration.
Proof. reflexivity. Qed.
Theorem parsed_fa12_batch_same : forall primitive txs stack fuel,
  FullVM_WIP.run primitive fuel [FullVM_WIP.Iter parsed_fa12_iteration] (FullVM_WIP.VList txs :: stack) =
  FullVM_WIP.run primitive fuel [FullVM_WIP.Iter FA12LoopBody.iteration] (FullVM_WIP.VList txs :: stack).
Proof. intros; rewrite fa12_iteration_matches; reflexivity. Qed.
Example ingress_full_source_matches : parsed_ingress_full = AdapterAuthorization.ingress_full.
Proof. reflexivity. Qed.
Example egress_full_source_matches : parsed_egress_full = AdapterAuthorization.egress_full.
Proof. reflexivity. Qed.
Example ingress_route_matches : parsed_ingress_route = AdapterRoute.ingress_build parsed_ingress_reject.
Proof. reflexivity. Qed.
Example egress_route_matches : parsed_egress_route = AdapterRoute.egress_build parsed_egress_reject.
Proof. reflexivity. Qed.
Example ticket_init_matches : parsed_ticket_init = TicketInit.init_code.
Proof. reflexivity. Qed.
Example ticket_final_matches : parsed_ticket_final = TicketFinal.final_code.
Proof. reflexivity. Qed.
Example ticket_iteration_matches : parsed_ticket_iteration = TicketLoopBody.ticket_iteration.
Proof. reflexivity. Qed.
Theorem parsed_ticket_batch_success_and_accounting : forall
  primitive verify unpack handle operation issuer contents txs old held credit ops next finalheld finalcredit finalops total,
  (forall tx old0 bound balance next0 rest, verify tx old0 = Some (bound,balance,next0) ->
    primitive "SAPLING_VERIFY_UPDATE" (tx :: old0 :: rest) =
      Some (FullVM_WIP.VSome (FullVM_WIP.VPair bound (FullVM_WIP.VPair (FullVM_WIP.VInt balance) next0)) :: rest)) ->
  (forall bytes recipient rest, unpack bytes = Some recipient ->
    primitive "UNPACK_address" (bytes :: rest) = Some (FullVM_WIP.VSome recipient :: rest)) ->
  (forall recipient receiver rest, handle recipient = Some receiver ->
    primitive "CONTRACT_ticket" (recipient :: rest) = Some (FullVM_WIP.VSome receiver :: rest)) ->
  (forall issuer0 contents0 quantity left right rest,
    primitive "SPLIT_ticket" (FullVM_WIP.VTicket issuer0 contents0 quantity :: FullVM_WIP.VPair (FullVM_WIP.VNat left) (FullVM_WIP.VNat right) :: rest) =
      Some (TicketPrimitives.split_ticket (FullVM_WIP.VTicket issuer0 contents0 quantity) left right :: rest)) ->
  (forall ticket receiver rest, primitive "TRANSFER_ticket" (ticket :: FullVM_WIP.VMutez 0 :: receiver :: rest) =
    Some (operation ticket receiver :: rest)) ->
  TicketMixedBatch.ticket_trace verify unpack handle operation issuer contents txs old held credit ops
    next finalheld finalcredit finalops total ->
  forall asset frame,
  FullVM_WIP.run primitive 138 [FullVM_WIP.Iter parsed_ticket_iteration]
    (FullVM_WIP.VList txs :: old :: held :: FullVM_WIP.VNat credit :: asset :: FullVM_WIP.VList ops :: frame) =
    Some (next :: finalheld :: FullVM_WIP.VNat finalcredit :: asset :: FullVM_WIP.VList finalops :: frame) /\\
  (Z.of_nat (TicketMixedBatch.held_quantity held) - Z.of_nat credit - total =
   Z.of_nat (TicketMixedBatch.held_quantity finalheld) - Z.of_nat finalcredit)%Z.
Proof.
  intros; split.
  - rewrite ticket_iteration_matches. eapply TicketMixedBatch.unbounded_successful_ticket_batch; eauto.
  - eapply TicketMixedBatch.ticket_trace_credit_adjusted_conservation; eauto.
Qed.
Print Assumptions parsed_ticket_batch_success_and_accounting.
Example ticket_batch_and_final_matches :
  FullVM_WIP.Iter parsed_ticket_iteration :: parsed_ticket_final =
  FullVM_WIP.Iter TicketLoopBody.ticket_iteration :: TicketFinal.final_code.
Proof. rewrite ticket_iteration_matches, ticket_final_matches; reflexivity. Qed.
Example ticket_full_matches :
  parsed_ticket_init ++ FullVM_WIP.Iter parsed_ticket_iteration :: parsed_ticket_final =
  TicketCompleteSuccess.full_code.
Proof. rewrite ticket_init_matches, ticket_iteration_matches, ticket_final_matches; reflexivity. Qed.
Example ticket_withdrawal_matches : parsed_ticket_withdrawal = TicketWithdrawal.ticket_withdrawal.
Proof. reflexivity. Qed.
Example fa2_full_private_matches :
  parsed_fa2_full = FA2PrivateSuccess.full_private_code parsed_fa2_public.
Proof. reflexivity. Qed.
Example fa2_public_success_matches : parsed_fa2_public = FA2PublicSuccess.public_code.
Proof. reflexivity. Qed.
Example fa2_full_public_success_matches : parsed_fa2_full = FA2PublicSuccess.full_code.
Proof. rewrite fa2_full_private_matches, fa2_public_success_matches; reflexivity. Qed.
Example fa2_guard_matches : parsed_fa2_guard = FA2Boundary.zero_tez_guard.
Proof. reflexivity. Qed.
Example fa2_init_matches : parsed_fa2_init = FA2Boundary.initialize.
Proof. reflexivity. Qed.
Example fa2_private_post_matches : forall nonprivate, parsed_fa2_private_post nonprivate = FA2Boundary.private_post nonprivate.
Proof. reflexivity. Qed.
Example fa2_canonical_matches : parsed_fa2_loop_body = FA2Combined.canonical_iteration.
Proof. reflexivity. Qed.
Example fa2_positive_matches : parsed_fa2_positive = FA2LoopBody.positive_iteration.
Proof. reflexivity. Qed.
Theorem parsed_fa2_positive_updates : forall
  verify unpack pack primitive tx old_state bound_data balance new_state recipient deposits withdrawals frame,
  (forall bound r rest, unpack bound = Some r -> primitive "UNPACK_address" (bound :: rest) = Some (FullVM_WIP.VSome r :: rest)) ->
  (forall r rest, primitive "PACK_address" (r :: rest) = Some (FullVM_WIP.VBytes (pack r) :: rest)) ->
  (forall tx0 old bound bal next rest, verify tx0 old = Some (bound, bal, next) -> primitive "SAPLING_VERIFY_UPDATE" (tx0 :: old :: rest) = Some (FullVM_WIP.VSome (FullVM_WIP.VPair bound (FullVM_WIP.VPair (FullVM_WIP.VInt bal) next)) :: rest)) ->
  verify tx old_state = Some (bound_data, balance, new_state) ->
  (0 < balance)%Z -> unpack bound_data = Some recipient -> List.length (pack recipient) = 28%nat ->
  FullVM_WIP.run primitive 90 parsed_fa2_loop_body
    (tx :: old_state :: deposits :: FullVM_WIP.VList withdrawals :: frame) =
  Some (new_state :: deposits :: FullVM_WIP.VList
    (FullVM_WIP.VPair recipient (FullVM_WIP.VNat (Z.to_nat balance)) :: withdrawals) :: frame).
Proof. intros; rewrite fa2_canonical_matches; unfold FA2Combined.canonical_iteration; eapply FA2LoopBody.verified_positive_iteration_with_updates_exact_stack; eauto. Qed.
Theorem parsed_fa2_positive_common_environment : forall
  verify unpack pack sender lookup update other tx old_state bound_data balance new_state recipient deposits withdrawals frame,
  verify tx old_state = Some (bound_data, balance, new_state) ->
  (0 < balance)%Z -> unpack bound_data = Some recipient -> List.length (pack recipient) = 28%nat ->
  FullVM_WIP.run (FA2Environment.primitive verify unpack pack sender lookup update other) 90 parsed_fa2_loop_body
    (tx :: old_state :: deposits :: FullVM_WIP.VList withdrawals :: frame) =
  Some (new_state :: deposits :: FullVM_WIP.VList
    (FullVM_WIP.VPair recipient (FullVM_WIP.VNat (Z.to_nat balance)) :: withdrawals) :: frame).
Proof.
  intros verify unpack pack sender lookup update other tx old_state bound_data balance new_state recipient deposits withdrawals frame HV HB HU HP.
  eapply (parsed_fa2_positive_updates verify unpack pack (FA2Environment.primitive verify unpack pack sender lookup update other)); try eassumption.
  - intros; rewrite FA2Environment.unpack_frame, H; reflexivity.
  - intros; apply FA2Environment.pack_frame.
  - intros; rewrite FA2Environment.verify_frame, H; reflexivity.
Qed.
Print Assumptions parsed_fa2_positive_common_environment.
Theorem parsed_unbounded_successful_mixed_batch : forall
  verify unpack pack sender lookup update other txs initial map ws final finalmap finalws,
  FA2MixedBatch.mixed_trace verify unpack pack sender lookup update txs initial map ws final finalmap finalws ->
  forall frame,
  FullVM_WIP.run (FA2Environment.primitive verify unpack pack sender lookup update other) 129
    [FullVM_WIP.Iter parsed_fa2_loop_body]
    (FullVM_WIP.VList txs :: initial :: map :: FullVM_WIP.VList ws :: frame) =
  Some (final :: finalmap :: FullVM_WIP.VList finalws :: frame).
Proof.
  intros; rewrite fa2_canonical_matches.
  eapply FA2MixedBatch.unbounded_successful_mixed_batch; eauto.
Qed.
Print Assumptions parsed_unbounded_successful_mixed_batch.
Theorem parsed_fa2_iter_composes : forall
  (primitive : String.string -> FullVM_WIP.stack -> option FullVM_WIP.stack)
  (step : FullVM_WIP.value -> FullVM_WIP.stack -> option FullVM_WIP.stack) fuel,
  (forall x s, FullVM_WIP.run primitive (S fuel) parsed_fa2_loop_body (x :: s) = step x s) ->
  forall xs s,
    FullVM_WIP.run primitive (S (S fuel)) [FullVM_WIP.Iter parsed_fa2_loop_body]
      (FullVM_WIP.VList xs :: s) = FullVM_WIP.iterate step xs s.
Proof. intros; eapply LoopInduction.source_loop_unbounded; eauto. Qed.
Print Assumptions parsed_fa2_iter_composes.
Print Assumptions parsed_fa2_positive_updates.
Print Assumptions parsed_vm_reverse_unbounded.
Print Assumptions parsed_nonpositive_empty.
Print Assumptions parsed_nonpositive_nonempty.
'''
with tempfile.TemporaryDirectory(prefix='sapling-coq-') as tmp:
    path = Path(tmp)
    shutil.copyfile(HERE / 'FullVM_WIP.v', path / 'FullVM_WIP.v')
    shutil.copyfile(HERE / 'TicketPrimitives.v', path / 'TicketPrimitives.v')
    shutil.copyfile(HERE / 'FA2Nonpositive.v', path / 'FA2Nonpositive.v')
    shutil.copyfile(HERE / 'FA2LoopBody.v', path / 'FA2LoopBody.v')
    shutil.copyfile(HERE / 'FA2DepositBody.v', path / 'FA2DepositBody.v')
    shutil.copyfile(HERE / 'FA2Combined.v', path / 'FA2Combined.v')
    shutil.copyfile(HERE / 'FA2Environment.v', path / 'FA2Environment.v')
    shutil.copyfile(HERE / 'LoopInduction.v', path / 'LoopInduction.v')
    shutil.copyfile(HERE / 'FA2MixedBatch.v', path / 'FA2MixedBatch.v')
    shutil.copyfile(HERE / 'FA2Boundary.v', path / 'FA2Boundary.v')
    shutil.copyfile(HERE / 'FA2PrivateSuccess.v', path / 'FA2PrivateSuccess.v')
    shutil.copyfile(HERE / 'FA2Operations.v', path / 'FA2Operations.v')
    shutil.copyfile(HERE / 'FA2Map.v', path / 'FA2Map.v')
    shutil.copyfile(HERE / 'FA2MapFuel.v', path / 'FA2MapFuel.v')
    shutil.copyfile(HERE / 'FA2DepositFuel.v', path / 'FA2DepositFuel.v')
    shutil.copyfile(HERE / 'FA2PublicSuccess.v', path / 'FA2PublicSuccess.v')
    shutil.copyfile(HERE / 'FA2SenderMap.v', path / 'FA2SenderMap.v')
    shutil.copyfile(HERE / 'FA12LoopBody.v', path / 'FA12LoopBody.v')
    shutil.copyfile(HERE / 'FA12MixedBatch.v', path / 'FA12MixedBatch.v')
    shutil.copyfile(HERE / 'FA12Boundary.v', path / 'FA12Boundary.v')
    shutil.copyfile(HERE / 'TicketWithdrawal.v', path / 'TicketWithdrawal.v')
    shutil.copyfile(HERE / 'TicketLoopBody.v', path / 'TicketLoopBody.v')
    shutil.copyfile(HERE / 'TicketMixedBatch.v', path / 'TicketMixedBatch.v')
    shutil.copyfile(HERE / 'TicketFinal.v', path / 'TicketFinal.v')
    shutil.copyfile(HERE / 'TicketPostBatch.v', path / 'TicketPostBatch.v')
    shutil.copyfile(HERE / 'TicketInit.v', path / 'TicketInit.v')
    shutil.copyfile(HERE / 'TicketCompleteSuccess.v', path / 'TicketCompleteSuccess.v')
    shutil.copyfile(HERE / 'AdapterRoute.v', path / 'AdapterRoute.v')
    shutil.copyfile(HERE / 'AdapterAuthorization.v', path / 'AdapterAuthorization.v')
    shutil.copyfile(HERE / 'AdapterParsedInverse.v', path / 'AdapterParsedInverse.v')
    shutil.copyfile(HERE / 'FA2StepInverse.v', path / 'FA2StepInverse.v')
    shutil.copyfile(HERE / 'FA2FullExtract.v', path / 'FA2FullExtract.v')
    shutil.copyfile(HERE / 'FA2TraceShape.v', path / 'FA2TraceShape.v')
    shutil.copyfile(HERE / 'FA2FullInverse.v', path / 'FA2FullInverse.v')
    shutil.copyfile(HERE / 'FA2OutputInverse.v', path / 'FA2OutputInverse.v')
    shutil.copyfile(HERE / 'FA2ParsedInverse.v', path / 'FA2ParsedInverse.v')
    shutil.copyfile(HERE / 'TicketInitInverse.v', path / 'TicketInitInverse.v')
    shutil.copyfile(HERE / 'TicketStepInverse.v', path / 'TicketStepInverse.v')
    shutil.copyfile(HERE / 'TicketPostInverse.v', path / 'TicketPostInverse.v')
    shutil.copyfile(HERE / 'TicketFullInverse.v', path / 'TicketFullInverse.v')
    shutil.copyfile(HERE / 'TicketParsedInverse.v', path / 'TicketParsedInverse.v')
    shutil.copyfile(HERE / 'FA12AddressGuardInverse.v', path / 'FA12AddressGuardInverse.v')
    shutil.copyfile(HERE / 'FA12LoopExtract.v', path / 'FA12LoopExtract.v')
    shutil.copyfile(HERE / 'FA12StepInverse.v', path / 'FA12StepInverse.v')
    shutil.copyfile(HERE / 'FA12FullInverse.v', path / 'FA12FullInverse.v')
    shutil.copyfile(HERE / 'FA12ParsedInverse.v', path / 'FA12ParsedInverse.v')
    extra_modules = ('InternalQueue.v', 'ManagerBatch.v', 'QueueExamples.v',
                     'MichelineRaw.v', 'MichelinePrograms.v', 'TypeInferenceWIP.v',
                     'DeclarativeSourceTyping.v', 'TypedVMSubset.v',
                     'MichelineRoundtrip.v', 'SelfCallShape.v',
                     'AssetLedger.v', 'SaplingNotes.v', 'SaplingIntegerLift.v', 'PoolCollateral.v', 'CollateralCallTree.v',
                     'QueueIdentityExamples.v', 'FA12ParsedCollateral.v',
                     'FA2ParsedCollateral.v', 'TicketParsedCollateral.v')
    for filename in extra_modules:
        if filename != 'MichelinePrograms.v':
            shutil.copyfile(HERE / filename, path / filename)
    (path / 'MichelinePrograms.v').write_text(render_programs({
        'fa12': fa12_data, 'fa2': data, 'ticket': ticket_data,
        'ingress': adapter_data['ingress'], 'egress': adapter_data['egress']}))
    (path / 'SourceLink.v').write_text(coq)
    programs = [('fa12', fa12_code), ('fa2', code), ('tickets', ticket_code)]
    source_programs = 'From Coq Require Import List String ZArith.\nImport ListNotations.\nOpen Scope string_scope.\nRequire Import FullVM_WIP.\n'
    for label, program in programs:
        translated, opaque = translate_program(program)
        source_programs += f'Definition {label}_program : list FullVM_WIP.instruction := {translated}.\n'
        print(f'WIP {label} instruction import (types erased): {sum(opaque.values())} opaque nodes {dict(opaque)}', flush=True)
    (path / 'SourcePrograms.v').write_text(source_programs)
    for filename in ('FullVM_WIP.v', 'TicketPrimitives.v', 'FA2Nonpositive.v', 'FA2LoopBody.v', 'FA2DepositBody.v', 'FA2Combined.v', 'FA2Environment.v', 'LoopInduction.v', 'FA2MixedBatch.v', 'FA2Boundary.v', 'FA2PrivateSuccess.v', 'FA2Operations.v', 'FA2Map.v', 'FA2MapFuel.v', 'FA2DepositFuel.v', 'FA2SenderMap.v', 'FA12LoopBody.v', 'FA12MixedBatch.v', 'FA12Boundary.v', 'FA2PublicSuccess.v', 'TicketWithdrawal.v', 'TicketLoopBody.v', 'TicketMixedBatch.v', 'TicketFinal.v', 'TicketPostBatch.v', 'TicketInit.v', 'TicketCompleteSuccess.v', 'AdapterRoute.v', 'AdapterAuthorization.v', 'FA12AddressGuardInverse.v', 'FA12LoopExtract.v', 'FA12StepInverse.v', 'FA12FullInverse.v', 'FA2StepInverse.v', 'FA2FullExtract.v', 'FA2TraceShape.v', 'FA2FullInverse.v', 'FA2OutputInverse.v', 'TicketInitInverse.v', 'TicketStepInverse.v', 'TicketPostInverse.v', 'TicketFullInverse.v', 'SourcePrograms.v', 'SourceLink.v', 'FA12ParsedInverse.v', 'AdapterParsedInverse.v', 'FA2ParsedInverse.v', 'TicketParsedInverse.v') + extra_modules:
        subprocess.run([args.coqc, filename], cwd=path, check=True)
    subprocess.run([args.coqchk, '-silent', 'FullVM_WIP', 'TicketPrimitives', 'FA2Nonpositive', 'FA2LoopBody', 'FA2DepositBody', 'FA2Combined', 'FA2Environment', 'LoopInduction', 'FA2MixedBatch', 'FA2Boundary', 'FA2PrivateSuccess', 'FA2Operations', 'FA2Map', 'FA2MapFuel', 'FA2DepositFuel', 'FA2SenderMap', 'FA12LoopBody', 'FA12MixedBatch', 'FA12Boundary', 'FA2PublicSuccess', 'TicketWithdrawal', 'TicketLoopBody', 'TicketMixedBatch', 'TicketFinal', 'TicketPostBatch', 'TicketInit', 'TicketCompleteSuccess', 'AdapterRoute', 'AdapterAuthorization', 'FA12AddressGuardInverse', 'FA12LoopExtract', 'FA12StepInverse', 'FA12FullInverse', 'FA2StepInverse', 'FA2FullExtract', 'FA2TraceShape', 'FA2FullInverse', 'FA2OutputInverse', 'TicketInitInverse', 'TicketStepInverse', 'TicketPostInverse', 'TicketFullInverse', 'SourcePrograms', 'SourceLink', 'FA12ParsedInverse', 'AdapterParsedInverse', 'FA2ParsedInverse', 'TicketParsedInverse'] + [Path(name).stem for name in extra_modules], cwd=path, check=True)
    for key, original in original_paths.items():
        if original.read_bytes() != original_bytes[key]:
            raise SystemExit(f'{key} source changed during verification; rerun against final bytes')
    def version(binary):
        return subprocess.run([binary, '--version'], check=True, text=True, capture_output=True).stdout.strip()
    def ast_hash(ast):
        return hashlib.sha256(json.dumps(ast, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    protocols = json.loads(subprocess.run(common + ['rpc', 'get', '/chains/main/blocks/head/protocols'],
                                          check=True, text=True, capture_output=True).stdout)
    for label, binary in [('octez_client', args.client), ('coqc', args.coqc), ('coqchk', args.coqchk)]:
        if binary_hash(binary) != tool_hashes[label]:
            raise SystemExit(f'{label} executable changed during verification; rerun with stable tools')
    if sorted([*HERE.glob('*.v'), *HERE.glob('*.py')]) != proof_inputs or any(
        hashlib.sha256(p.read_bytes()).hexdigest() != proof_input_hashes[p.name] for p in proof_inputs
    ):
        raise SystemExit('verification sources changed during verification; rerun after they stabilize')
    manifest = {
        'verification_input_sha256': proof_input_hashes,
        'source_sha256': {'fa12': fa12_digest, 'fa2': digest, 'ticket': ticket_digest, 'ingress': adapter_digest['ingress'], 'egress': adapter_digest['egress']},
        'canonical_parsed_json_sha256': {'fa12': ast_hash(fa12_data), 'fa2': ast_hash(data), 'ticket': ast_hash(ticket_data), 'ingress': ast_hash(adapter_data['ingress']), 'egress': ast_hash(adapter_data['egress'])},
        'octez_client': {'path': str(Path(shutil.which(args.client) or args.client).resolve()),
                         'version': version(args.client), 'binary_sha256': tool_hashes['octez_client']},
        'coqc': {'version': version(args.coqc), 'binary_sha256': tool_hashes['coqc']},
        'coqchk': {'version': version(args.coqchk), 'binary_sha256': tool_hashes['coqchk']},
        'mockup_head_protocols': protocols,
        'scope': 'Partial fragment theorems and unproved WIP interpreter; see verification README.'}
    args.artifacts_dir.mkdir(parents=True, exist_ok=True)
    output = Path(tempfile.mkdtemp(prefix='run-', dir=args.artifacts_dir))
    for label, ast in [('fa12', fa12_data), ('fa2', data), ('ticket', ticket_data), ('ingress', adapter_data['ingress']), ('egress', adapter_data['egress'])]:
        (output / (label + '.micheline.json')).write_text(json.dumps(ast, sort_keys=True, separators=(',', ':')))
    for filename in ('FullVM_WIP.v', 'TicketPrimitives.v', 'FA2Nonpositive.v', 'FA2LoopBody.v', 'FA2DepositBody.v', 'FA2Combined.v', 'FA2Environment.v', 'LoopInduction.v', 'FA2MixedBatch.v', 'FA2Boundary.v', 'FA2PrivateSuccess.v', 'FA2Operations.v', 'FA2Map.v', 'FA2MapFuel.v', 'FA2DepositFuel.v', 'FA2SenderMap.v', 'FA12LoopBody.v', 'FA12MixedBatch.v', 'FA12Boundary.v', 'FA2PublicSuccess.v', 'TicketWithdrawal.v', 'TicketLoopBody.v', 'TicketMixedBatch.v', 'TicketFinal.v', 'TicketPostBatch.v', 'TicketInit.v', 'TicketCompleteSuccess.v', 'AdapterRoute.v', 'AdapterAuthorization.v', 'FA12AddressGuardInverse.v', 'FA12LoopExtract.v', 'FA12StepInverse.v', 'FA12FullInverse.v', 'FA2StepInverse.v', 'FA2FullExtract.v', 'FA2TraceShape.v', 'FA2FullInverse.v', 'FA2OutputInverse.v', 'TicketInitInverse.v', 'TicketStepInverse.v', 'TicketPostInverse.v', 'TicketFullInverse.v', 'SourcePrograms.v', 'SourceLink.v', 'FA12ParsedInverse.v', 'AdapterParsedInverse.v', 'FA2ParsedInverse.v', 'TicketParsedInverse.v') + extra_modules:
        shutil.copy2(path / filename, output / filename)
        vo = path / (Path(filename).stem + '.vo')
        if vo.exists(): shutil.copy2(vo, output / vo.name)
    manifest['proof_artifact_sha256'] = {
        artifact.name: hashlib.sha256(artifact.read_bytes()).hexdigest()
        for artifact in sorted(output.iterdir()) if artifact.is_file()}
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'Proof artifacts saved in new directory: {output}')
print(f'PASS FA2 source pin and reversal-fragment shape gate: {digest}')
print(f'PASS FA1.2 source pin and final-merge shape gate: {fa12_digest}')
print(f'PASS ticket source pin and identity-guard shape gate: {ticket_digest}')
print('PASS parsed FA1.2 successful-call trace converse under complete framed primitive specifications')
print('PASS parsed adapter successful-call guard and fixed-route converses under complete framed primitive specifications')
print('PASS parsed FA2 successful-call trace, reachable single-sender accounting and output converse under explicit primitive specifications')
print('PASS parsed ticket successful-call identity, zero-credit trace, output and quantity converse under explicit primitive specifications')
print('PASS Coq-checked parsed FA2 reversal using fixed structural fuel for arbitrary list lengths')
print('PASS Coq-checked parsed FA2 nonpositive-branch empty/nonempty bound-data guard')
print('PASS Coq-checked parsed FA2 positive iteration with explicit Sapling/packing callbacks')
print('PASS Coq-checked arbitrary-length parsed FA2 successful mixed traces, under explicit callbacks')
print('PASS Coq-checked arbitrary-length canonical FA2 ITER composition CONDITIONAL on each-step refinement and named callbacks')
print('WIP all script instruction nodes translated into partial VM; type annotations erased and opaque primitives have NO behavior theorem')
print('LIMIT: source parser/translation and Michelson/Octez correspondence are trusted; whole-pool invariants are unproved.')

print('PASS raw-tree encoding/decoding roundtrip and injectivity for arbitrary finite trees')
print('PASS five exact raw source imports and connected whole-body WIP type computations; checker soundness remains open')
print('PASS conditional source-trace collateral and manager call-tree composition; native context/issuer/ownership refinement remains open')

print('PASS distinct operation nonces retain repeated payloads and settle twice; nonce replay rolls back')

print('PASS whole parsed-model calls derive FA source certificates and ticket stored/owned bounds without trace/output premises')

print('PASS all five connected declarative source typing derivations; native typing correspondence remains open')
print('PASS 15-form typed-model erasure simulation and source-linked FA1.2 slice; native execution correspondence remains open')
print('PASS modular-to-integer Sapling balance and liability under explicit bounded witness extraction; native cryptographic/context soundness remains open')
