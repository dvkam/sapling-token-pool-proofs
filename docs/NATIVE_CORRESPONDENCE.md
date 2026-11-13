# Native Octez correspondence: feasibility checkpoint

The current Coq results do not establish correspondence with the actual Octez OCaml interpreter. The five complete source-bound derivations and successful-execution converses are theorems about a modeled Michelson semantics. Their input normalization and source translation, typed primitive behavior, native interpreter, operation dispatcher, and external asset execution remain outside those theorems.

`TypedVMSubset.v` is a checked incremental bridge between two Coq models: a type-indexed instruction/program semantics and the existing `FullVM_WIP` interpreter. It covers 15 pure instruction forms for arbitrary finite compositions and includes the exact FA1.2 source slice `DUP; DUP; ABS`. Coq 8.18 checks the theorem statements and proof terms; the verification manifest records their exact source hashes. It does not import native OCaml or prove an OCaml simulation.

## Available translation infrastructure

* The [historical Tezos OCaml-to-Coq project](https://gitlab.com/formal-land/coq-tezos-of-ocaml) checkout examined is commit `4cb66f28a71bfd3dc4460d8db90595a76fa4a8ea` (2022-12-16). Its README specifies Coq 8.14 and a protocol compatible with its translator. Its translated historical Sapling instruction delegates verification to `Alpha_context.Sapling.verify_update`. The historical Alpha interpreter validity lemmas in `src/Proto_alpha/Proofs/Script_interpreter.v` are admitted. Other historical protocol directories contain simulation work; their presence does not establish a theorem for the current protocol.
* The project's [limitations](https://formal-land.gitlab.io/coq-tezos-of-ocaml/docs/limitations/) describe manual validation of translation, assumed definitions, and a GADT cast axiom unsound in general. These must be audited as trusted assumptions, not treated as a proof of faithful translation.
* Current [rocq-of-ocaml](https://github.com/formal-land/rocq-of-ocaml) upstream commit `1ac69a72ea1b09e22f14608032ee7ff4bfeea7d3` (2026-05-18) requires OCaml >= 5.4 and < 5.7 in its opam file. The target was built with OCaml 5.3.0. Its README states GADT support is partial and axiom-free GADT compilation remains open, and requires a compiled Merlin-configured project. No successful translation of this pinned target or semantic-preservation proof has been established here. An older compatible translator or port might be explored, but compatibility alone would not prove correctness.

## Existing Michelson semantics

Mi-Cho-Coq's dev branch, commit
`6262ab76a6fc491246054c9327f5d393082b47e2`, has typed Sapling and ticket
instructions. Its `SAPLING_VERIFY_UPDATE` returns an optional pair of balance
and state. These contracts require the current optional triple of bound data,
balance and state. Its ticket split semantics also permits zero components,
which the pinned native protocol rejects. That branch requires Coq 8.14-8.16.
It is a possible foundation after an audited update, rather than a checker for
these exact contracts today. The older master branch lacks those instructions.
See [Mi-Cho-Coq dev](https://gitlab.com/nomadic-labs/mi-cho-coq/-/tree/6262ab76a6fc491246054c9327f5d393082b47e2).

K-Michelson commit `822c9dd294ceeaef822b7e354def79bcf30e25dc` has ticket
instructions but lacks Sapling rules in its inspected syntax and semantics.
Its ticket split rule also accepts zero components. See
[K-Michelson](https://github.com/runtimeverification/michelson-semantics/tree/822c9dd294ceeaef822b7e354def79bcf30e25dc).

A complete contract proof relative to a trusted, updated Michelson
specification can leave the Octez runtime and cryptographic implementation in
the trusted base. It still needs a faithful source-to-program link and full
typed instruction semantics for the actual programs. This differs from proving
that Octez's OCaml implementation implements that specification. Neither
complete theorem has been established at this checkpoint.

## Work needed to close the native gap

1. Produce an auditable translation of the exact pinned protocol source and compiled dependency interfaces, with explicit treatment of GADTs, casts, monadic effects, exceptions, gas, and divergence. Establish translation correctness or explicitly accept a reviewed translator and its exact assumptions as part of the trusted base.
2. Connect the actual Michelson parser and typed instruction constructors to the five raw source trees and their declarations. Prove source import, typing, stack/value representation and interpreter execution agree with the established Coq semantics, including every executed opcode and error path; position-based translation overrides cannot substitute for this proof.
3. Connect actual lazy storage, operation identifiers and ordering, internal-call execution, gas and failure/rollback to the source-linked accounting and queue theorems. Verify the relevant token implementation behavior or state its exact separate assumptions.
4. State and justify the trusted boundary for Sapling proof verification, root/nullifier storage, native encodings, cryptography and Rust/FFI. Connect the note liability and ledger representations to real reachable contexts. Compilers, runtime, operating system and cryptographic soundness remain explicit trust assumptions unless separately verified.

These are substantive engineering and proof obligations, not a missing test or permission. No inspected tool currently supplies the complete native correspondence for these five contracts, and no full actual-Octez verification is claimed.
