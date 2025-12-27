# Structural Explainability: Exchange Protocol

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
![Build Status](https://github.com/civic-interconnect/ExchangeProtocol/actions/workflows/ci.yml/badge.svg)
[![Check Links](https://github.com/civic-interconnect/ExchangeProtocol/actions/workflows/links.yml/badge.svg)](https://github.com/civic-interconnect/ExchangeProtocol/actions/workflows/links.yml)

> Lean 4 formalization of the exchange protocol schemas.

## What This Formalizes

This repository provides machine-checked proofs of properties in the Exchange Protocol:

1. **Core Types** (`Core.lean`)
   - RecordEnvelope with attestations, timestamps, CTags
   - Entity records with multiple identifier schemes
   - Relationship records (bilateral/multilateral)
   - Exchange records with provenance chains

2. **Graph Structures** (`Graphs.lean`)
   - CEP graphs of entities, relationships, exchanges
   - Well-formedness predicates
   - Provenance chain extraction
   - Theorems: finite chains, resolvable references

3. **Attestation Properties** (`Attestations.lean`)
   - Multi-party attestation
   - Temporal ordering of attestations
   - Theorems: well-formed records have attestations

4. **Context Tags** (`CTags.lean`)
   - Interpretive metadata without identity changes
   - GDPR-relevant properties (human review, disputed facts)
   - Theorems: CTags preserve canonical identity

## Key Theorems
```lean
-- Every exchange has traceable provenance
theorem exchange_has_provenance

-- Exchange chains are finite (no infinite loops)
axiom exchange_chain_finite

-- Well-formed records have attestations
theorem wellformed_has_attestation

-- CTags preserve canonical identity
axiom ctags_preserve_identity
```

## Build and Run

```shell
lake update
lake build
lake exe verify
```

## Citation

[CITATION.cff](./CITATION.cff)

## License

[MIT](./LICENSE)