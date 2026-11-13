#!/usr/bin/env python3
"""Report instruction coverage required for the exact three scripts."""
import argparse, collections, json, subprocess
from pathlib import Path
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--contracts', type=Path, required=True)
parser.add_argument('--client', required=True)
parser.add_argument('--base-dir', type=Path, required=True)
args = parser.parse_args()
for name in ('sapling_contract_fa_1_2.tz', 'sapling_contract_fa_2.tz', 'sapling_contract_tickets.tz'):
    command = [args.client, '--base-dir', str(args.base_dir), '--mode', 'mockup', 'convert', 'script',
               str(args.contracts / name), 'from', 'michelson', 'to', 'json']
    data = json.loads(subprocess.run(command, text=True, check=True, capture_output=True).stdout)
    code = next(x['args'][0] for x in data if x.get('prim') == 'code')
    operations = []
    def visit(value):
        if isinstance(value, list):
            for item in value: visit(item)
        elif isinstance(value, dict):
            prim = value.get('prim', '')
            if prim.isupper(): operations.append(prim)
            visit(value.get('args', []))
    visit(code)
    print(f'{name}: {len(operations)} instruction nodes, {len(set(operations))} distinct')
    print('  ' + ' '.join(f'{name}:{count}' for name, count in sorted(collections.Counter(operations).items())))
