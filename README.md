# Structural Explainability: Exchange Protocol

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
![Build Status](https://github.com/civic-interconnect/ExchangeProtocol/actions/workflows/ci.yml/badge.svg)
[![Check Links](https://github.com/civic-interconnect/ExchangeProtocol/actions/workflows/links.yml/badge.svg)](https://github.com/civic-interconnect/ExchangeProtocol/actions/workflows/links.yml)

> Lean 4 formalization of the exchange protocol schemas.

## What This Formalizes

This repository provides a Lean 4 formalization
of the structural core of the Exchange Protocol,
including canonical record schemas for
entities, relationships, and exchanges;
a shared RecordEnvelope; 
retention-policy data shapes; 
and basic graph-oriented data structures.
The code machine-checks the well-formedness and 
typing of these structures and verifies that 
the protocol's core representations are 
internally consistent and composable, 
without embedding causal, normative, or policy interpretations.

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