module bar where

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

variable
  ℓ₁ ℓ₂ : Level

postulate
  lemma : ℓ₁ ⊔ ℓ₂ ≡ ℓ₂

foo : Set (suc (ℓ₁ ⊔ ℓ₂)) → Set (suc ℓ₂)
foo {ℓ₁}{ℓ₂} A = subst (λ ℓ → {! Set ℓ  !}) (lemma {ℓ₁}{ℓ₂}) {! A  !}