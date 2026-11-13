# Sapling modular balance to integer liability

This arithmetic proof does not establish native verifier correctness.
Run the complete verification command documented in README.md to check
`SaplingIntegerLift.v` with the other source-linked modules. The runner
records its exact source and checked-object hashes. The accompanying
`sapling-integer-lift-evidence.json` identifies the reviewed native and
dependency sources; these are evidence for the bounds, not an audited
translation of those sources.

## What is proved

For at most 5208 consumed input notes and 2019 created output notes, each with
value in `[0, 2^64)`, and a signed-64-bit public balance `b`, divisibility of
`sum(inputs) - sum(outputs) - b` by the Jubjub subgroup order implies the
ordinary integer equation `sum(inputs) - sum(outputs) = b`. The discrepancy is
strictly between `-q` and `q`; a bounded multiple of `q` must be zero.

The order is
`q = 0x0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb7`
`= 6554484396890773809930967563523245729705921265872317281365359162392183254199`.
It is the Jubjub prime-subgroup scalar order, **not** the BLS12-381 circuit
scalar-field modulus. The worst positive discrepancy allowed by the broader
signed-64-bit hypothesis is `96079866507916199586728`; the magnitude of the
worst negative discrepancy is `37253199656856439486492`. Both are much smaller
than `q`. No primality axiom is needed for this integer arithmetic theorem.

The native specialization uses the actual public balance bound
`[-2100000000000000, 2100000000000000]`. A witness partition and freshness law,
together with modular binding, yields the existing `note_transition` and then
`liability(after) = liability(before) - b`. No reserve or backing conclusion
is assumed. A regression exhibits that congruence alone permits discrepancy
`q` if the range hypotheses are dropped.

`accepted_verifier_integer_liability` exposes the remaining accepted-verifier
witness extraction assumption separately. It requires membership/partition,
freshness/uniqueness, ranges/counts, and modular balance; it does not assume
the integer balance equation or the liability equation. It is an idealized
soundness interface; probabilistic/adversarial security is not formalized.

## Exact implementation evidence

The following Octez paths are pinned to base
`932c237495cfd795872bd70ef9ecc8af59868bab`; the source evidence manifest records
the actual current mirror bytes, which must be checked when integrating.

- [sapling_validator.ml](https://gitlab.com/tezos/tezos/-/blob/932c237495cfd795872bd70ef9ecc8af59868bab/src/proto_alpha/lib_protocol/sapling_validator.ml#L48): lines 52-57 assert input/output limits 5208/2019; lines 98-115 require final binding verification and return the transaction's balance and updated state. The encoding independently sets those limits in `src/lib_sapling/core.ml:806-807,856-857`.
- [rustzcash.ml](https://gitlab.com/tezos/tezos/-/blob/932c237495cfd795872bd70ef9ecc8af59868bab/src/lib_sapling/rustzcash.ml#L376): lines 376-387 define MAX_MONEY and `valid_balance`; lines 633-642 enforce it before the FFI. The comment giving a wider specification interval is not the accepted native range.
- [FFI mapping](https://gitlab.com/tezos/tezos/-/blob/932c237495cfd795872bd70ef9ecc8af59868bab/src/lib_sapling/bindings/rustzcash_ctypes_bindings.ml#L167) selects `librustzcash_sapling_final_check`. [Rust implementation](https://gitlab.com/tezos/tezos/-/blob/932c237495cfd795872bd70ef9ecc8af59868bab/src/rustzcash_deps/src/rustzcash.rs#L686) performs `Amount::from_i64` again before `ctx.final_check`.
- [script_interpreter.ml](https://gitlab.com/tezos/tezos/-/blob/932c237495cfd795872bd70ef9ecc8af59868bab/src/proto_alpha/lib_protocol/script_interpreter.ml#L1431): accepted balance becomes `Script_int.of_int64`, not an Int64 arithmetic accumulator. The pools' Michelson ABS is integer ABS. In any event the native MAX_MONEY gate excludes signed minimum before the Rust `checked_abs` conversion.
- `src/rust_deps/Cargo.lock` pins `jubjub 0.9.0`, `zcash_primitives 0.6.0`, `zcash_proofs 0.6.0`, and `bellman 0.13.1`. The manifest hashes each inspected registry source, independently of documentation prose.
- [zcash_proofs 0.6.0 circuit](https://docs.rs/crate/zcash_proofs/0.6.0/source/src/circuit/sapling.rs): `expose_value_commitment`, lines 75-116, allocates 64 Boolean bits and uses those same bits in both the value commitment and note contents (spend lines 232-246; output lines 406-410). `bellman`'s `u64_into_boolean_vec_le` allocates exactly 64 `AllocatedBit`s. This is a circuit bound, unlike the client-only constructors' MAX_MONEY bound.
- The spend circuit's conditional root check (lines 343-358) allows zero-valued dummy inputs without membership. A ghost extraction must omit such dummy spends, or account for them without claiming they consumed a live note. Positive-valued inputs still require actual membership, nullifier/authorization and context reasoning.
- [zcash_proofs verifier](https://docs.rs/crate/zcash_proofs/0.6.0/source/src/sapling/verifier.rs) adds spend commitments, subtracts output commitments, subtracts `b * G_value` and verifies a binding signature under `G_randomness` (lines 141-174). `sapling/mod.rs:14-35` implements signed value multiplication via checked absolute value and optional negation. This gives the sign `inputs - outputs = public balance`, agreeing with the Octez Forge implementation and native shielding tests.
- [jubjub Fr](https://docs.rs/crate/jubjub/0.9.0/source/src/fr.rs) states the exact order above. [zcash_primitives constants](https://docs.rs/crate/zcash_primitives/0.6.0/source/src/constants.rs) declares both commitment generators as `SubgroupPoint`; tests derive them from distinct `v` and `r` messages under `Zcash_cv` group-hash personalization.

## Cryptographic and context boundary

Distinct hash-derived generators do not prove algebraic independence: a cyclic
group always has a discrete-log relation. The required security property is
that an efficient adversary cannot exploit a known relation or forge the
binding signature to make an accepted set of valid commitment openings violate
the modular equation. The appropriate joint circuit/commitment/signature
soundness/extraction assumption remains external, including trusted parameter
generation, exact verifying keys, curve encodings/subgroup handling and FFI
correctness. The Coq file neither proves these cryptographic claims nor derives
them merely from successful boolean verification.

The note witness also requires commitment identity/freshness, authenticated
membership, nullifier uniqueness, the recent-root rule and a representation of
the actual context/diff. It is not a public enumeration of all encrypted notes.
Source correspondence from native circuit/FFI execution to this witness,
typed Michelson refinement, actual issuer ledger semantics, asset custody and
atomic internal-operation execution remain separate obligations. This increment
closes integer wraparound reasoning within that interface; it does not close
those obligations or establish full actual-contract verification.
