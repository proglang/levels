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
- `SSF-UP-IR.agda`:
- `SSF-UP-EH.agda`:

#### Comparison Matrices 

##### Glossary 

| Code | Description |
|-----|---------------------|
| SSF | Stratified System F |
| EH  | Extended Hierarchy  |
| IR  | Induction Recursion |

##### Object Language

| Name    | Universe Hierarchy | Universe Polymorphism |
|---------|--------------------|-----------------------|
| SSF     | yes                | no                    |
| SSF-EH  | yes                | yes                   |
| SSF-IR  | yes                | yes                   |

##### Formalization Methods

| Name    | Level Magic | Induction Recursion | Extended Hierarchy |
|---------|-------------|---------------------|--------------------|
| SSF     | yes         | no                  | no                 |
| SSF-EH  | yes (*)     | no                  | yes                | 
| SSF-IR  | no          | yes                 | no                 |


##### Problems 

| Name    | Suffers Subst Hell Unnecessarily | Hits Hierarchy Limit |
|---------|----------------------------------|----------------------|
| SSF     | no                               | no                   |
| SSF-EH  | no (*)                           | no                   |
| SSF-IR  | yes                              | no                   |

## Solver Laws

```agda
open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)

infix 40 ω^_+_
postulate
  ω^_+_ : (ℓ₁ ℓ₂ : Level) → Level

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  
postulate 
  β-suc-zero     : suc zero ≡ ω^ zero + zero                                           -- by definition 
  β-suc-ω        : suc (ω^ ℓ₁ + ℓ₂) ≡ ω^ ℓ₁ + suc ℓ₂                                   -- by definition   
  distributivity : ω^ ℓ + (ℓ₁ ⊔ ℓ₂) ≡ ω^ ℓ + ℓ₁ ⊔ ω^ ℓ + ℓ₂                            -- ω^_+_ distributes _⊔_
  subsumption    : ℓ ⊔ ω^ ℓ₁ + ℓ₂ ≡ ω^ ℓ₁ + ℓ₂              -- if ℓ occurs in ℓ₁ or ℓ₂ -- _⊔_ subsumes ω^_+_
```
