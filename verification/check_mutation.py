#!/usr/bin/env python3
"""Demonstrate a type-correct source mutation is rejected by the AST gate."""
import argparse
import hashlib
from pathlib import Path
import subprocess
import sys
import tempfile

here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--contract', type=Path, required=True)
parser.add_argument('--client', required=True)
parser.add_argument('--base-dir', type=Path, required=True)
parser.add_argument('--coqc', default='coqc')
parser.add_argument('--coqchk', default='coqchk')
args = parser.parse_args()
source = args.contract.read_text()
old = 'NIL (pair address (list (pair address nat nat)));\n           SWAP;\n           ITER { CONS };'
new = old.replace('ITER { CONS }', 'ITER { DROP }')
if source.count(old) != 1:
    raise SystemExit('Mutation anchor changed; inspect the source before proceeding')
with tempfile.TemporaryDirectory(prefix='sapling-coq-mutation-') as tmp:
    mutant = Path(tmp) / 'bad_order.tz'
    mutant.write_text(source.replace(old, new, 1))
    subprocess.run([args.client, '--base-dir', str(args.base_dir), '--mode', 'mockup',
                    'typecheck', 'script', str(mutant)], check=True, capture_output=True)
    digest = hashlib.sha256(mutant.read_bytes()).hexdigest()
    cmd = [sys.executable, str(here / 'check_order.py'), '--contract', str(mutant),
           '--client', args.client, '--base-dir', str(args.base_dir), '--coqc', args.coqc,
           '--coqchk', args.coqchk, '--expected-sha256', digest]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode == 0 or 'Source shape changed: expected both reversal fragments' not in result.stderr:
        raise SystemExit(f'Mutation was not rejected for the expected AST reason: {result.stdout} {result.stderr}')
print(f'PASS: type-correct final ITER {{ DROP }} mutant rejected by AST check: {digest}')
print('This demonstrates change detection, not a Coq proof of the mutant\'s execution.')

ticket_source = here.parent / 'contracts/sapling_contract_tickets.tz'
text = ticket_source.read_text()
old = 'DUP 7;\n           COMPARE;\n           EQ;'
if text.count(old) != 1:
    raise SystemExit('Ticket identity mutation anchor changed; inspect the source')
with tempfile.TemporaryDirectory(prefix='sapling-ticket-mutation-') as tmp:
    mutant = Path(tmp) / 'bad_identity.tz'
    mutant.write_text(text.replace(old, old.replace('EQ;', 'NEQ;'), 1))
    subprocess.run([args.client, '--base-dir', str(args.base_dir), '--mode', 'mockup',
                    'typecheck', 'script', str(mutant)], check=True, capture_output=True)
    digest = hashlib.sha256(mutant.read_bytes()).hexdigest()
    cmd = [sys.executable, str(here / 'check_order.py'), '--contract', str(args.contract),
           '--ticket-contract', str(mutant), '--expected-ticket-sha256', digest,
           '--client', args.client, '--base-dir', str(args.base_dir), '--coqc', args.coqc,
           '--coqchk', args.coqchk]
    result = subprocess.run(cmd, capture_output=True, text=True)
    expected_rejection = ('unsupported ticket initialization nodes' in result.stderr and "'NEQ'" in result.stderr)
    if result.returncode == 0 or not expected_rejection:
        raise SystemExit(f'Ticket mutant not rejected for expected AST reason: {result.stdout} {result.stderr}')
print(f'PASS: type-correct paid-ticket EQ to NEQ mutant rejected by initialization translator: {digest}')

fa12_source = here.parent / 'contracts/sapling_contract_fa_1_2.tz'
text = fa12_source.read_text()
old = 'DIP { NIL operation; SWAP; ITER { CONS } };'
if text.count(old) != 1:
    raise SystemExit('FA1.2 final reversal mutation anchor changed; inspect the source')
with tempfile.TemporaryDirectory(prefix='sapling-fa12-mutation-') as tmp:
    mutant = Path(tmp) / 'bad_fa12_order.tz'
    mutant.write_text(text.replace(old, old.replace('ITER { CONS }', 'ITER { DROP }'), 1))
    subprocess.run([args.client, '--base-dir', str(args.base_dir), '--mode', 'mockup',
                    'typecheck', 'script', str(mutant)], check=True, capture_output=True)
    digest = hashlib.sha256(mutant.read_bytes()).hexdigest()
    cmd = [sys.executable, str(here / 'check_order.py'), '--contract', str(args.contract),
           '--fa12-contract', str(mutant), '--expected-fa12-sha256', digest,
           '--client', args.client, '--base-dir', str(args.base_dir), '--coqc', args.coqc,
           '--coqchk', args.coqchk]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode == 0 or 'FA1.2 final order fragment shape changed' not in result.stderr:
        raise SystemExit(f'FA1.2 mutant not rejected for expected AST reason: {result.stdout} {result.stderr}')
print(f'PASS: type-correct FA1.2 withdrawal-reversal ITER {{ DROP }} mutant rejected by AST check: {digest}')

old = 'DIG 3;\n                   SIZE;\n                   PUSH nat 0;\n                   COMPARE;\n                   EQ;'
if source.count(old) != 1:
    raise SystemExit('FA2 nonpositive bound-data guard anchor changed; inspect the source')
with tempfile.TemporaryDirectory(prefix='sapling-fa2-bound-mutation-') as tmp:
    mutant = Path(tmp) / 'bad_bound_data.tz'
    mutant.write_text(source.replace(old, old.replace('EQ;', 'NEQ;'), 1))
    subprocess.run([args.client, '--base-dir', str(args.base_dir), '--mode', 'mockup',
                    'typecheck', 'script', str(mutant)], check=True, capture_output=True)
    digest = hashlib.sha256(mutant.read_bytes()).hexdigest()
    cmd = [sys.executable, str(here / 'check_order.py'), '--contract', str(mutant),
           '--expected-sha256', digest, '--client', args.client, '--base-dir', str(args.base_dir),
           '--coqc', args.coqc, '--coqchk', args.coqchk]
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode == 0 or 'FA2 nonpositive bound-data guard shape changed' not in result.stderr:
        raise SystemExit(f'FA2 bound-data mutant not rejected for expected AST reason: {result.stdout} {result.stderr}')
print(f'PASS: type-correct FA2 nonpositive bound-data EQ to NEQ mutant rejected by AST check: {digest}')

old = 'UNPACK address;'
if source.count(old) != 1:
    raise SystemExit('FA2 positive recipient mutation anchor changed; inspect the source')
with tempfile.TemporaryDirectory(prefix='sapling-fa2-recipient-mutation-') as tmp:
    mutant = Path(tmp) / 'bad_recipient.tz'
    mutant.write_text(source.replace(old, 'DROP; SELF_ADDRESS; SOME;', 1))
    subprocess.run([args.client, '--base-dir', str(args.base_dir), '--mode', 'mockup',
                    'typecheck', 'script', str(mutant)], check=True, capture_output=True)
    digest = hashlib.sha256(mutant.read_bytes()).hexdigest()
    cmd = [sys.executable, str(here / 'check_order.py'), '--contract', str(mutant),
           '--expected-sha256', digest, '--client', args.client, '--base-dir', str(args.base_dir),
           '--coqc', args.coqc, '--coqchk', args.coqchk]
    result = subprocess.run(cmd, capture_output=True, text=True)
    expected_rejection = ('unsupported canonical FA2 loop nodes' in result.stderr and "'SELF_ADDRESS'" in result.stderr)
    if result.returncode == 0 or not expected_rejection:
        raise SystemExit(f'FA2 recipient mutant not rejected for expected source translation reason: {result.stdout} {result.stderr}')
print(f'PASS: type-correct FA2 recipient-substitution mutant rejected by canonical-loop translator: {digest}')

# These source mutations preserve Michelson typing but violate the intended
# fixed beneficiary and one-shot state. Rejection is an exact AST gate,
# not a proof of the mutants' behavior.
adapter_dir = here.parent / 'contracts'
adapter_mutations = [
    ('egress', 'DUP 4; SWAP;\n       NIL (ticket',
     'DUP 2; SWAP;\n       NIL (ticket', 'Adapter egress beneficiary selector changed'),
    ('ingress', 'DROP; PUSH bool True', 'DROP; PUSH bool False',
     'Adapter ingress one-shot flag changed'),
]
for label, old, new, expected in adapter_mutations:
    source = (adapter_dir / f'sapling_fa21_{label}.tz').read_text()
    if source.count(old) != 1:
        raise SystemExit(f'Adapter {label} mutation anchor changed; inspect the source')
    with tempfile.TemporaryDirectory(prefix=f'sapling-{label}-mutation-') as tmp:
        mutant = Path(tmp) / f'{label}.tz'
        mutant.write_text(source.replace(old, new, 1))
        subprocess.run([args.client, '--base-dir', str(args.base_dir), '--mode', 'mockup',
                        'typecheck', 'script', str(mutant)], check=True, capture_output=True)
        digest = hashlib.sha256(mutant.read_bytes()).hexdigest()
        cmd = [sys.executable, str(here / 'check_order.py'), '--contract', str(args.contract),
               f'--adapter-{label}', str(mutant), f'--expected-{label}-sha256', digest,
               '--client', args.client, '--base-dir', str(args.base_dir), '--coqc', args.coqc,
               '--coqchk', args.coqchk]
        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode == 0 or expected not in result.stderr:
            raise SystemExit(f'Adapter {label} mutant not rejected for expected source reason: {result.stdout} {result.stderr}')
    print(f'PASS: type-correct adapter {label} mutant rejected by exact source gate: {digest}')
