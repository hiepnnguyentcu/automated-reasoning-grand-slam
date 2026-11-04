# Chapter 16: Cryptographic Assurance

Part 5: Real Systems.

## Objective

Prove functional correctness and side-channel properties of real cryptographic code.

## Proof of mastery

Verify a real implementation of a cryptographic primitive against a formal specification.

## Topics

| Topic | Objective |
|---|---|
| [Cryptography for Verifiers](cryptography-for-verifiers/) | Explain the primitives, security definitions and attacks needed to state verification goals. |
| [Functional Correctness](functional-correctness/) | Prove an implementation equal to its specification using Cryptol and SAW. |
| [Constant-Time Verification](constant-time-verification/) | Define constant-time security and verify it for a small implementation. |
| [Verified Libraries](verified-libraries/) | Compare how HACL*, Fiat Crypto, s2n-bignum and AWS-LC structure their proofs. |
| [Continuous Proof](continuous-proof/) | Keep a proof running in continuous integration as its code changes. |
| [Protocol Verification](protocol-verification/) | Model a key exchange protocol in Tamarin and prove its secrecy properties. |

## Main materials

- Barbosa et al., SoK: Computer-Aided Cryptography, IEEE S&P 2021.
- [Boneh and Shoup, A Graduate Course in Applied Cryptography.](https://toc.cryptobook.us/)
- Chudnov et al., Continuous Formal Verification of Amazon s2n, CAV 2018.
