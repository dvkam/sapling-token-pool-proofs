# Sapling token pool proofs

Coq proofs about five Michelson smart contracts for Tezos: three Sapling shielded pools backed by a token, and two adapters that route an FA2.1 token through tickets. A Python runner ties each proof to the exact contract source and checks everything with the Coq kernel.

The proofs are about a model of Michelson written in Coq. They do not prove anything about the Octez interpreter itself. Read [what the proofs do not show](#what-the-proofs-do-not-show) before you rely on them.

## Where the contracts come from

This is an independent project. Nomadic Labs and the Tezos Foundation did not publish it and have not reviewed or endorsed it.

The contracts belong to the Tezos Octez project. Octez is developed on GitLab at [tezos/tezos](https://gitlab.com/tezos/tezos) and its code is under the MIT licence. The copyright notices from Octez are reproduced in [LICENSE](LICENSE).

- The three pool contracts continue Raphaël Cauderlier's draft merge request [!7252](https://gitlab.com/tezos/tezos/-/merge_requests/7252) at Nomadic Labs, written for Octez issue [#4488](https://gitlab.com/tezos/tezos/-/work_items/4488). This repository contains modified versions of his contracts.
- The two adapter contracts are new. They were written with these proofs and follow the ticket export and import interface of [TZIP-26](https://gitlab.com/tezos/tzip/-/blob/f0acad1b8215e3e07c879546c186488a0aa86963/proposals/tzip-26/tzip-26.md).
- The modified pools and the adapters are not part of Octez. Two draft merge requests propose them: [!23143](https://gitlab.com/tezos/tezos/-/merge_requests/23143) for the pools and [!23144](https://gitlab.com/tezos/tezos/-/merge_requests/23144) for the adapters. Neither is merged. If Octez accepts different versions, the proofs here apply only to the files in `contracts/`.
- All references to Octez source files in `docs/` point at Octez commit [`932c2374`](https://gitlab.com/tezos/tezos/-/tree/932c237495cfd795872bd70ef9ecc8af59868bab).

[contracts/README.md](contracts/README.md) lists each file with its origin and hash.

## What the proofs show

Each result starts from the fact that a whole contract call succeeded in the model. It then derives what must have happened. No result assumes the trace, the output or the safety property it concludes.

| Contract | Result | File |
| --- | --- | --- |
| FA1.2 pool | A successful call emits exactly the expected token transfers, deposits before withdrawals. The pool's reserve grows by at least as much as its shielded liability. | `FA12ParsedCollateral.v` |
| FA2 pool | The same result. The proof also derives when the pool calls the token contract and when it does not. | `FA2ParsedCollateral.v` |
| Ticket pool | The pool accepts only tickets of its fixed ticketer and contents, consumes every unit it receives, and keeps a stored quantity that covers its shielded liability. | `TicketParsedCollateral.v` |
| Adapters | A successful ingress call came from the issuer, carried the fixed asset, forwarded the stored proof to the fixed pool and marked the ingress used. A successful egress call came from the pool and sent the ticket to the fixed beneficiary. | `AdapterParsedInverse.v`, `AdapterAuthorization.v` |
| Call tree | If every step of a manager batch fits one of three stated classes, the pool is backed when the batch commits. | `CollateralCallTree.v` |
| Sapling arithmetic | Within the note and balance limits of Octez, the balance equation modulo the Jubjub group order implies the same equation over the integers. | `SaplingIntegerLift.v` |

"Backed" means the pool's token reserve is at least the total value of unspent shielded notes.

Supporting files prove that the Micheline encoding of each contract round-trips, give a typing derivation for each contract in a second model, and relate a typed model to the untyped one for 15 instructions. [docs/MODULES.md](docs/MODULES.md) describes every file.

## What the proofs do not show

- They do not cover the Octez interpreter, type checker, gas accounting or operation scheduler. `verification/FullVM_WIP.v` is a 171-line model, and nothing proves that Octez behaves like it.
- A Python script translates each contract into that model. The translation is trusted. The runner only checks that the translated program equals the program the proofs talk about.
- The model does not define `SAPLING_VERIFY_UPDATE`, `COMPARE`, `PACK`, `UNPACK`, `CONTRACT`, `TRANSFER_TOKENS` and a few other instructions. The theorems take their behaviour as hypotheses.
- The Sapling cryptography is a hypothesis. The theorems assume that an accepted transaction spends existing notes and creates new ones with the stated balance.
- The token contract is a hypothesis. The theorems assume it moves exactly the requested amount. A token that takes fees, rebases or freezes transfers breaks the backing result.
- A failed call and an ill-formed program both end in the same "no result" state. The proofs describe successful calls only.
- No one has audited the contracts or the proofs.

[docs/NATIVE_CORRESPONDENCE.md](docs/NATIVE_CORRESPONDENCE.md) lists the work a proof about Octez itself would need.

## Repository layout

| Path | Content |
| --- | --- |
| `contracts/` | The five Michelson contracts the proofs are about. |
| `verification/*.v` | 64 Coq files. |
| `verification/*.py` | The runner, the translators and the mutation check. |
| `docs/` | Notes on each module, the address encoding, the Sapling arithmetic and the gap to Octez. |

## Run the checks

A full run took 8 minutes on a desktop machine. It compiles and kernel-checks 67 Coq modules, rejects seven deliberately broken contracts, then checks the original contracts again.

### Requirements

- Linux. The runs recorded here used Ubuntu 24.04 on amd64.
- Python 3.11 or newer.
- Coq 8.18.0, with `coqc` and `coqchk`.
- An `octez-client` that knows the Alpha protocol. The runner uses it to parse and type-check the contracts. The checks pass with the Octez 25.3 release client and with a client built from Octez commit `932c2374`. Other versions are untested. See the [Octez installation guide](https://octez.tezos.com/docs/introduction/howtoget.html).

### Install Coq 8.18.0

On Ubuntu 24.04 the distribution package is the right version:

```sh
sudo apt install coq
```

To avoid installing it system-wide, extract the packages into a directory of your choice. This needs about 600 MB:

```sh
export COQ_DIR="$HOME/coq-8.18"
mkdir -p "$COQ_DIR/debs" "$COQ_DIR/root"
cd "$COQ_DIR/debs"
apt-get download 'coq=8.18.0+dfsg-1build2' 'libcoq-core-ocaml=8.18.0+dfsg-1build2' \
  'libcoq-stdlib=8.18.0+dfsg-1build2' 'libfindlib-ocaml=1.9.6-1build4' 'libzarith-ocaml=1.13-2build4'
for f in ./*.deb; do dpkg-deb -x "$f" "$COQ_DIR/root"; done
cat > "$COQ_DIR/findlib.conf" <<EOF
path="$COQ_DIR/root/usr/lib/ocaml:/usr/lib/ocaml"
destdir="$COQ_DIR/root/usr/lib/ocaml"
EOF
export OCAMLFIND_CONF="$COQ_DIR/findlib.conf"
export COQLIB="$COQ_DIR/root/usr/lib/ocaml/coq"
export COQC="$COQ_DIR/root/usr/bin/coqc"
export COQCHK="$COQ_DIR/root/usr/bin/coqchk"
```

The recorded runs used the second method. With the system package, set `COQC=coqc` and `COQCHK=coqchk`.

### Create a mockup

The runner needs a local mockup directory. It sends nothing to a network.

```sh
export OCTEZ_CLIENT=/path/to/octez-client
export MOCKUP="$HOME/sapling-proofs-mockup"
"$OCTEZ_CLIENT" --protocol ProtoALphaALphaALphaALphaALphaALphaALphaALphaDdp3zK \
  --base-dir "$MOCKUP" --mode mockup create mockup
```

### Run

From the repository root:

```sh
python3 verification/verify.py --client "$OCTEZ_CLIENT" --base-dir "$MOCKUP" \
  --coqc "$COQC" --coqchk "$COQCHK"
```

A successful run ends with this line, followed by a line that starts with `LIMIT:` and repeats the main limits:

```text
PASS: scoped Coq proofs checked before and after a type-correct source mutation was detected.
```

The runner does three things in order.

1. It hashes the five contracts and stops if a hash differs from the pinned value. It parses them with `octez-client`, translates them, generates the Coq statements that link the sources to the proofs, compiles everything with `coqc` and rechecks the compiled proofs with `coqchk`.
2. It makes seven small changes to the contracts, one at a time. Each changed contract still type-checks in Octez but breaks a property, for example by dropping the withdrawal list. The runner requires each one to fail at a specific check.
3. It repeats the first step on the unchanged contracts.

Each successful run of the first step writes the generated Coq files, the compiled proofs and a manifest of hashes to a new directory under `.local/verification/`. Git ignores that directory.

## Contract hashes

| File | SHA-256 |
| --- | --- |
| `sapling_contract_fa_1_2.tz` | `ac29f6ddc86e055eeee8fe7e1aacbf58216cc68090952c3c4fa065924f08ebf1` |
| `sapling_contract_fa_2.tz` | `4527dbc0bfcbbb795a099349ee1207ea65a9a98ca83e10331b82946f04535163` |
| `sapling_contract_tickets.tz` | `efa68bf8c66c12c65008cbf5871d494574c3a7a21ebb450c653b2fc6734ee5cb` |
| `sapling_fa21_ingress.tz` | `22eef9d75bd6b8e0f9f934f6c8737d4c7c717a81d98dd64a363529b1ca7e1d9a` |
| `sapling_fa21_egress.tz` | `0a102ec7e76fdf0b4bf083e019b2173f7d6933ad4600e29155b83fe905762281` |

If you change a contract, the runner stops. Review the proofs against your change before you update a pin in `verification/check_order.py`.

## Licence and credits

Everything here is under the MIT licence. See [LICENSE](LICENSE).

- The pool contracts derive from Octez and from Raphaël Cauderlier's work in !7252. The Octez copyright holders are Dynamic Ledger Solutions, Nomadic Labs, Metastate and Tarides.
- The adapter contracts, the Coq proofs and the Python tools were written for this repository.
- Tezos and Octez are names of their respective owners. This repository uses them to say what the contracts are for.
