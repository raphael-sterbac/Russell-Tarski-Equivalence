# Equivalence of Cumulative Universe Hierarchies in Dependent Type Theory

This repository contains the Rocq (Coq) formalization of the equivalence between Russell and Tarski presentations for a cumulative hierarchy of universes in dependent type theory. 

This work accompanies the talk at the TYPES conference by **Thierry Coquand and Raphaël Sterbac**.

## Overview

In dependent type theory, cummulative universes have two common presentations:
* **Russell-style**: Often regarded as an informal but user-friendly notation where types and universes are conflated.
* **Tarski-style**: A fully explicit presentation with decoding and lifting functions, which is mandatory to define Type Theory as a Generalised Algebraic Theory (GAT) and to provide rigorous semantics and models.

The goal of this project is to provide a modular, algorithmic proof of equivalence between these two presentations for a theory featuring dependent products, cumulative universes, and judgmental $\beta\eta$ conversion. Establishing this equivalence rigorously allows us to give models to Martin-Löf Type Theory (MLTT) with Russell universes directly.

## Formalization Structure

The formalization is written in Rocq/Coq (`main.v`) and revolves around a forgetful erasure map from the Tarski theory to the Russell theory. 

The file defines two parallel type systems using De Bruijn indices:
1.  `ty` / `term` / `WfContextDecl` / `TypingDecl`: The explicit Tarski system with lifting (`cLift`), universe codes (`cU`), and decoding (`Decode`).
2.  `russ_term` / `Russ_WfContextDecl` / `Russ_TypingDecl`: The implicit Russell system.

### Erasure Operation
We define an erasure operation (`erase_term`, `erase_ty`, `erase_context`) that strips the annotations from the Tarski system (decodings and liftings) to produce Russell terms. It is quite straightforward to see that this operation preserves derivations.

### Main Theorems

The core of the formalisation is dedicated to proving that this forgetful map has a well-defined inverse. 

**1. Uniqueness up to Erasure (Injectivity of Erasure)**
If two judgments in the Tarski system erase to the exact same syntactic Russell terms, then they are provably convertible in the Tarski system. 
* *Coq Lemmas*: `erase_inj_ty` and `erase_inj_term` (proven via explicit mutual fixpoints to guarantee termination).

**2. Equivalence (Section Theorem)**
If a judgment holds in the Russell system, there exists a unique (up to conversion) corresponding judgment in the Tarski system that erases back to it.
* *Coq Theorems*: `section_ctx`, `section_ty`, `section_term`, `section_conv`, and `section_conv_term`.

## Axioms and Assumptions

As outlined in the abstract, the equivalence proof fundamentally relies on the **normalisation and injectivity of type constructors** for the Tarski-style theory. While normalisation can be proven via an adaptation of the gluing technique, this specific Rocq formalization takes normalisation and injectivity of type formers (such as `PiInj` and `UInj`) as axioms to focus purely on the equivalence algorithms.

At the moment, the formalisation also puts all the subsitution and weakening lemmas as axioms. It would be great to recover them from a tool such as AutoSubst, to obtain a self-contained proof.

## Building the Project

To check the proofs, you will need a recent version of Rocq/Coq (tested on Rocq 9.1.0).

```bash
coqc main.v