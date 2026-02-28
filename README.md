# Equivalence of Cumulative Universe Hierarchies in Dependent Type Theory

This repository contains the Rocq formalization of the equivalence between Russell and Tarski presentations for a cumulative hierarchy of universes in dependent type theory. 

## Overview

In dependent type theory, cummulative universes have two common presentations. The Russell-style universes are often regarded as an informal  notation where types and universes are mixed. The Tarski-style is a fully explicit presentation with decoding and lifting functions, which is essential to define Type Theory as a Generalised Algebraic Theory (GAT) and to provide rigorous semantics and models.

The goal of this project is to provide a modular, algorithmic proof of equivalence between these two presentations for a theory featuring dependent products, cumulative universes, and judgmental $\beta\eta$ conversion. Establishing this equivalence rigorously allows us to give models to Martin-Löf Type Theory (MLTT) with Russell universes directly.

## Formalization Structure

The formalization is written in Rocq (`main.v`) and revolves around a forgetful erasure map from the Tarski theory to the Russell theory. 

### Project Layout
* `Syntax.v`: Grammars of the two systems and basic structures.
* `Typing.v`: Mutual inductive typing and conversion rules for both Tarski and Russell systems.
* `Utils.v`: Structural properties, inversion lemmas.
* `Erasure.v`: The erasure function (stripping Tarski-specific annotations) and the proof of its correction.
* `Equivalence.v`: The main equivalence result, including injectivity of erasure and the final theorem defining the section of the erasure.

### Main Theorems

The core of the formalisation is dedicated to proving that the erasure map has a well-defined inverse. We prove the two following essential results.

**Uniqueness up to Erasure (Injectivity of Erasure)**
If two judgments in the Tarski system erase to the exact same syntactic Russell terms, then they are provably convertible in the Tarski system. 
**Rocq Lemmas*: `erase_inj_ty` and `erase_inj_term` (proven via explicit mutual fixpoints to guarantee termination).

**Equivalence (Section Theorem)**
If a judgment holds in the Russell system, there exists a unique (up to conversion) corresponding judgment in the Tarski system that erases back to it.
**Rocq Theorems*: `section_ctx`, `section_ty`, `section_term`, `section_conv`, and `section_conv_term`.

## Axioms and Assumptions

As outlined in the abstract, the equivalence proof fundamentally relies on the **normalisation and injectivity of type constructors** for the Tarski-style theory. While normalisation can be proven via an adaptation of the gluing technique, this specific Rocq formalization takes normalisation and injectivity of type formers (such as `PiInj` and `UInj`) as axioms to focus purely on the equivalence algorithms.

At the moment, the formalisation also puts all the subsitution and weakening lemmas as axioms. It would be great to recover them from a tool such as AutoSubst, to obtain a self-contained proof.

## Building the Project

To check the proofs, you will need a recent version of Rocq/Coq (tested on Rocq 9.1.0).

```bash
rocq makefile -f _CoqProject -o Makefile

make