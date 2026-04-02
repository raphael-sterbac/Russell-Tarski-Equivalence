# Equivalence of Cumulative Universe Hierarchies in Dependent Type Theory

Rocq formalization of a proof of equivalence between Russell and Tarski presentations for a cumulative hierarchy of universes in dependent type theory. 

## Overview

In dependent type theory, cummulative universes have two common presentations. The Russell-style universes, where types and universes are mixed and coercions are implicit. The Tarski-style is a fully explicit presentation with decoding and lifting functions, which is essential to define Type Theory as a Generalised Algebraic Theory (GAT) and to provide rigorous semantics and models.

The goal of this project is to provide a modular, algorithmic proof of equivalence between these two presentations for a theory with dependent products, cumulative universes, and judgmental $\beta\eta$ conversion.

## Formalization Structure

The formalization is written in Rocq (`main.v`) and focuss on the erasure map from the Tarski theory to the Russell theory. The main result is proving that this erasure map admits a section.

### Project Layout
* `Syntax.v`: Grammars of the two systems and basic structures.
* `Typing.v`: Mutual inductive typing and conversion rules for both Tarski and Russell systems.
* `Utils.v`: Structural properties, inversion lemmas.
* `Erasure.v`: The erasure function (stripping Tarski-specific annotations) and the proof of its correction.
* `Equivalence.v`: The main equivalence result, including injectivity of erasure and the final theorem defining the section of the erasure.

### Main Theorems

We prove the two following essential results.

**Uniqueness up to Erasure (Injectivity of Erasure)**
If two judgments in the Tarski system erase to the same syntactic Russell terms, then they are provably convertible in the Tarski system. Rocq Lemmas: `erase_inj_ty` and `erase_inj_term`.

**Equivalence (Section Theorem)**
If a judgment holds in the Russell system, there exists a unique (up to conversion) corresponding judgment in the Tarski system that erases back to it. Rocq Theorems: `section_ctx`, `section_ty`, `section_term`, `section_conv`, and `section_conv_term`.

## Axioms and Assumptions

As outlined in the abstract, the equivalence proof fundamentally relies on the normalisation and injectivity of type constructors for the Tarski-style theory. While normalisation can be proven via an adaptation of the gluing technique, this formalization takes normalisation and injectivity of type formers (such as `PiInj` and `UInj`) as axioms to focus purely on the equivalence proofs.

At the moment, the formalisation also puts all the subsitution and weakening lemmas as axioms. It would be great to recover them from a tool such as AutoSubst, to obtain a fully self-contained proof.

## Building the Project

To check the proofs, you will need a recent version of Rocq/Coq (tested on Rocq 9.1.0).

```bash
rocq makefile -f _CoqProject -o Makefile

make