# Canonical recipient-length guard

This review is specific to Octez base `932c237495cfd795872bd70ef9ecc8af59868bab` and the pinned Alpha sources. The FA pools unpack the signed recipient; the egress adapter validates its stored beneficiary. Both repack the parsed address value and require 28 bytes. Checking an original supplied byte length would not establish the canonical entrypoint property.

`script_ir_unparser.ml:214` serializes an optimized address as `tup2 Destination.encoding Entrypoint.value_encoding`. `destination_repr.ml` includes contract, smart-rollup and ZK-rollup destinations. Each binary destination occupies 22 bytes:

| Destination | Bytes |
|---|---|
| Implicit account | Contract tag `00`, account-scheme tag, 20-byte public-key hash |
| Originated contract | Tag `01`, 20-byte contract hash, one padding byte |
| Smart rollup | Tag `03`, 20-byte rollup hash, one padding byte |
| ZK rollup | Tag `04`, 20-byte rollup hash, one padding byte |

Tag `02` is reserved for removed transaction rollups. The implicit scheme cases include tz1 through tz5. Feature-gated destinations are rejected when disabled; their accepted encoding does not acquire a different length.

`entrypoint_repr.ml:196` serializes the default entrypoint as an empty variable string and a named entrypoint as its name bytes. The address separator `%` is not added to that binary suffix. A valid non-default name is nonempty. `PACK address` then adds `05`, the Micheline bytes tag `0a` and a four-byte payload length. Hence canonical packed length is `6 + 22 + byte_length(entrypoint_name)`: 28 precisely for default and greater for a non-default entrypoint. This reasoning depends on these concrete destination and entrypoint encodings.

`script_ir_translator.ml:1679` applies the same destination feature checks to optimized and readable address inputs. Readable parsing splits at the first `%`; subsequent percent characters remain in the entrypoint name. The native tests retain `receive%part` exactly. The length check operates on repacking after this parsing, so alternate accepted input representations cannot bypass it by choosing a shorter original spelling.

The packing test that backs this review is not in this repository. It belongs to the example client proposed for Octez with the contracts, where `npm run test:packing` compares the client's tz1 to tz5 and KT1 encodings to native `hash data ... of type address`. Additional native-only vectors check both rollup tags with empty and `receive%part` suffixes, exact bytes-node framing, enabled ZK rollups and specific `Zk_rollup_disabled` rejection, plus a smart-rollup control in the disabled context. These are finite executable controls supporting the source case analysis, not a formal proof of `Data_encoding` or the native parser.

That example client supports implicit and KT1 recipients. The reference contracts' length guard checks entrypoints rather than selecting a destination family. Actual custody, spendability and delivery depend on the token issuer or typed receiver. This review makes no claim that every native address can receive or spend every asset. Review the guard and these tests whenever destination serialization or entrypoint encoding changes.
