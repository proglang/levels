# Supplement Material

## Dependencies

- `agda` version `2.7.0.1`: https://agda.readthedocs.io/en/v2.7.0.1/getting-started/installation.html
- `standard-library` version `2.1.1`: https://github.com/agda/agda-stdlib/blob/v2.1-release/doc/installation-guide.md

## Structure

### External Code

- `Ordinal.agda`: modified from "Three Equivalent Ordinal Notation Systems in Cubical Agda"[^1]
- `Universe.agda`: modified from "Generalized Universe Hierarchies and First-Class Universe Levels"[^2]

[^1]: https://arxiv.org/abs/1904.10759
[^2]: https://arxiv.org/abs/2103.00223

### Library Code

- `ExtendedHierarchy.agda`: Extended Level Hierarchy with support for levels up to ε₀
- `BoundQuantification.agda`: Bounded Level Quantification (with support for Extended Hierarchy) 

### Stratified System F Formalizations

- `SSF.agda`: Denotational Semantics for Stratified System F
- `SSF-UP-IR.agda`: Denotational Semantics for Stratified System F with Level Quantification using Induction Recursion 
- `SSF-UP-EH.agda`: Denotational Semantics for Stratified System F with Level Quantification using the Extended Level Hierarchy