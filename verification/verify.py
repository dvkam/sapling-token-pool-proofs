#!/usr/bin/env python3
"""Check the scoped Coq fragment, a real source mutant, then the fragment again."""
import argparse
from pathlib import Path
import subprocess
import sys

here = Path(__file__).resolve().parent
repository = here.parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--contract', type=Path, default=repository / 'contracts/sapling_contract_fa_2.tz')
parser.add_argument('--client', required=True)
parser.add_argument('--base-dir', type=Path, required=True)
parser.add_argument('--coqc', default='coqc')
parser.add_argument('--coqchk', default='coqchk')
parser.add_argument('--artifacts-dir', type=Path,
                    help='Parent for uniquely named proof-artifact directories')
args = parser.parse_args()
common = ['--contract', str(args.contract.resolve()), '--client', args.client,
          '--base-dir', str(args.base_dir.resolve()), '--coqc', args.coqc, '--coqchk', args.coqchk]
for script in ('check_order.py', 'check_mutation.py', 'check_order.py'):
    print(f'Running {script}', flush=True)
    artifact_option = ['--artifacts-dir', str(args.artifacts_dir.resolve())] if args.artifacts_dir and script == 'check_order.py' else []
    subprocess.run([sys.executable, str(here / script)] + common + artifact_option, check=True)
print('PASS: scoped Coq proofs checked before and after a type-correct source mutation was detected.')
print('LIMIT: all failure behavior, typed VM/Octez correspondence, external token execution, rollback and Sapling backing are NOT proved; pool success converses assume explicit primitive specifications and FA2 uses a concrete single-sender map model.')
