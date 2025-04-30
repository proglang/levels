Thank you for your thoughtful comments.

# Points raised by the reviewers

## A, B: no meta-theory

* The basis of our system is Kovacs's theory TTDL from *Generalized Universe Hierarchies...*. This paper established consistency.
* Subject reduction and substitution invariance (the pain points of *Type Theory with Explicit Universe Polymorphism* by Bezem et al) should not be affected by replacing the original level structure with another type-theoretic ordinal (which is what we do in the paper; we proved (it's in the Agda development, but not spelt out in the paper) that ordinals in CNF are type-theoretic ordinals in the sense of Kovacs's paper), but we were not aware of the lack of SR (mod cumulativity) for Agda pointed out by reviewer B.
* Further meta-theory, like canonicity and normalization, seems out of scope for this paper.

## A: related work

* noted, thanks for the pointers.

## A: System F

* note that we never say we treat System F, but *stratified System F* (SF), a predicative variant.
* we feel that SF is a simple system, in which we can demonstrate the problems without getting involved in the additional intricacies of a dependently typed system; arguably, getting to limit levels in SF may feel unnatural, but it's immediate in the system with level quantification in Section 5.
* a level-problem that appears naturally in Agda code is pointed out in Section 6.4: there is a simple encoding of a level bound in the data-structure representation of some environment structure, but the corresponding functional encoding lives in Set𝜔.

## A 244 correct by construction

This remark refers to the property of the CNF representation by Forsberg et al, which ensures that all constructed values are well-formed. 

## A Fig 13 infl-add

This law ended up in the paper by mistake. What is really needed (and proved in `ExtendedHierarchy.agda`) is this
structure:
```
data _∊_ : Level → Level → Set where
  id  : ∀ {ℓ : Level} → ℓ ∊ ℓ
  add : ∀ {ℓ ℓ₂ : Level} (ℓ₁ : Level) → ℓ ∊ ℓ₂ → ℓ ∊ ω^ ℓ₁ + ℓ₂ 
  exp : ∀ {ℓ ℓ₁ : Level} (ℓ₂ : Level) → ℓ ∊ ℓ₁ → ℓ ∊ ω^ ℓ₁ + ℓ₂

postulate
  subsumption : ℓ₁ ∊ ℓ₂ → ℓ₁ ⊔ ℓ₂ ≡ ℓ₂
```

# B lack of novelty

> *induction-recursion is less convenient than native universes* [...] *[10] spells out this point*

Correct, but all that is said in [10] is this single sentence: *The answer is that induction-recursion provides a deep embedding of universe features, which is usually less convenient to use than native features.*
We consider this sentence quite an understatement as the loss of convenience is so significant to render the deep embedding barely useful.

> continuing the above sentence *in Agda the support for ω+ω levels was similarly motivated*

We don't quite understand this statement. Can you give a reference, please?

