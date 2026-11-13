# Contracts

These five Michelson files are the exact inputs of the proofs. The runner hashes them before every run and stops if a hash differs from its pinned value.

They are reference contracts for Tezos Octez issue [#4488](https://gitlab.com/tezos/tezos/-/work_items/4488). None of them is part of Octez. Nobody has audited them. Do not deploy them with real assets on the strength of these proofs.

| File | Purpose | Origin |
| --- | --- | --- |
| `sapling_contract_fa_1_2.tz` | Shielded pool backed by an FA1.2 token. | Modified from Raphaël Cauderlier's draft [!7252](https://gitlab.com/tezos/tezos/-/merge_requests/7252), commit `dad20ce2d2f0`. |
| `sapling_contract_fa_2.tz` | Shielded pool backed by one token id of an FA2 contract. | Modified from the same draft. |
| `sapling_contract_tickets.tz` | Shielded pool backed by tickets of one fixed ticketer and contents. | Modified from the same draft. |
| `sapling_fa21_ingress.tz` | One-shot receiver. It takes a ticket exported by an FA2.1 issuer and shields it in the ticket pool with a stored proof. | New. |
| `sapling_fa21_egress.tz` | Receiver for withdrawals. It sends the ticket to the issuer's import entrypoint for a fixed beneficiary. | New. |

The changes to the three pools, compared with the draft, are these.

- A withdrawal signs a packed `address` as its recipient. The draft used a packed key hash.
- The FA1.2 and FA2 pools reject a recipient address that names an entrypoint.
- Deposits run before withdrawals within one call.
- The ticket pool stores its ticketer and ticket contents at origination and keeps them when it holds no ticket.

The original contracts are part of [Tezos Octez](https://gitlab.com/tezos/tezos) and are under the MIT licence. See [LICENSE](../LICENSE) for the copyright notices.
