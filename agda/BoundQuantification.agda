{-# OPTIONS --allow-unsolved-metas #-}
module BoundQuantification where

module foo where
  open import Data.Nat hiding (_≤_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
  private variable
    ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : ℕ

  data _≤_ : ℕ → ℕ → Set where
    ≤-id  : ∀ ℓ → ℓ ≤ ℓ
    ≤-suc : ℓ₁ ≤ ℓ₂ → ℓ₁ ≤ suc ℓ₂
    ≤-lub : ∀ ℓ₂ → ℓ ≤ ℓ₁ → ℓ₃ ≡ ℓ₁ ⊔ ℓ₂ → ℓ ≤ ℓ₃
  
  ≤-lublub : ℓ₁ ≤ ℓ₃ → ℓ₂ ≤ ℓ₃ → (ℓ₁ ⊔ ℓ₂) ≤ ℓ₃
  ≤-lublub (≤-id _) (≤-id _) = {!   !}
  ≤-lublub (≤-id .(suc _)) (≤-suc y) = {!   !}
  ≤-lublub (≤-id _) (≤-lub ℓ₂ y refl) = {! ≤-lublub (≤-id ?) y   !}
  ≤-lublub (≤-suc x) (≤-id .(suc _)) = {!   !}
  ≤-lublub (≤-suc x) (≤-suc y) = {!   !}
  ≤-lublub (≤-suc x) (≤-lub ℓ₂ y x₁) = {!   !}
  ≤-lublub (≤-lub ℓ₂ x x₁) (≤-id _) = {!   !}
  ≤-lublub (≤-lub ℓ₂ x x₁) (≤-suc y) = {!   !}
  ≤-lublub (≤-lub ℓ₂ x x₁) (≤-lub ℓ₃ y x₂) = {!   !}

open import Level
open import ExtendedHierarchy using (ω^_+_; cast; β-suc-zero; β-suc-ω; subsumption₁₀)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import Data.Sum using (_⊎_; inj₁; inj₂)
  

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  Λ Λ′ Λ₁ Λ₂ Λ₃ Λ₄ : Level

-- Ordering on Levels ---------------------------------------------------------
data _≤_ : Level → Level → Set where
  ≤-id  : ∀ ℓ → ℓ ≤ ℓ
  ≤-suc : ℓ₁ ≤ ℓ₂ → ℓ₃ ≡ suc ℓ₂ → ℓ₁ ≤ ℓ₃
  -- ≤-lub : ∀ ℓ₂ → ℓ ≤ ℓ₁ → ℓ ≤ (ℓ₁ ⊔ ℓ₂)

_<_ : Level → Level → Set
_<_ ℓ₁ ℓ₂ = suc ℓ₁ ≤ ℓ₂ 

-- the important thing is, that the left hand side of the inequalities does not 
-- differ to the ones in the hypotheses, 
-- such that we can recurse in the BoundLift / bound-lift / bound-unlift functions 

postulate
  ≤-add : ∀ ℓ₁ → ℓ ≤ ℓ₂ → ℓ ≤ ω^ ℓ₁ + ℓ₂ 
  ≤-exp : ∀ ℓ₂ → ℓ ≤ ℓ₁ → ℓ ≤ ω^ ℓ₁ + ℓ₂ 
  
  ≤-suc-ω : ∀ ℓ₁ ℓ₂ → ℓ ≤ ω^ ω^ ℓ₁ + ℓ₂ + ℓ₃ → suc ℓ ≤ ω^ ℓ₁ + ℓ₂ 
  ≤-lublub : ℓ₁ ≤ ℓ₃ → ℓ₂ ≤ ℓ₃ → (ℓ₁ ⊔ ℓ₂) ≤ ℓ₃
  -- unification fails, no way to match on level?
  -- no injectivity of suc on levels

-- these two could easily be added to the actual relation 
-- if agda would support the extended level hierarchy

≤-sucsuc : ℓ₁ ≤ ℓ₂ → suc ℓ₁ ≤ suc ℓ₂
≤-sucsuc (≤-id ℓ)       = ≤-id (suc ℓ)
≤-sucsuc (≤-suc x refl) = ≤-suc (≤-sucsuc x) refl

-- Bounded Quantification -----------------------------------------------------
record BoundLevel (Λ : Level) : Set where
  constructor _,_  
  field 
    # : Level
    #<Λ : # < Λ

open BoundLevel public

bound : BoundLevel Λ → Level
bound {Λ} _ = Λ

-- Lifiting using Ordering ----------------------------------------------------

BoundLift  : ℓ ≤ Λ → Set ℓ → Set Λ
BoundLift (≤-id ℓ)                   A = Lift ℓ A
BoundLift (≤-suc {ℓ₂ = ℓ₂} ℓ≤Λ refl) A = Lift (suc ℓ₂) (BoundLift ℓ≤Λ A)

-- BoundLift (<₄ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} ℓ≤Λ) A = 
--   cast (subsumption₁₀ {ℓ = ℓ₁} {ℓ₁ = ℓ₂}) (Lift (ω^ ℓ₂ + ℓ₁) (BoundLift ℓ≤Λ A))
-- the need for the casts makes it impossible to add <₄ and <₅

bound-lift : ∀ (ℓ≤Λ : ℓ ≤ Λ) → {A : Set ℓ} → A → BoundLift ℓ≤Λ A
bound-lift (≤-id ℓ)       a = lift a
bound-lift (≤-suc ℓ≤Λ refl)    a = lift (bound-lift ℓ≤Λ a)
-- bound-lift {ℓ} (<₄ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} ℓ≤Λ) a = {! lift (bound-lift ℓ≤Λ a) !}

bound-unlift : ∀ (ℓ≤Λ : ℓ ≤ Λ) → {A : Set ℓ} → BoundLift ℓ≤Λ A → A
bound-unlift (≤-id ℓ)       (Level.lift a) = a
bound-unlift (≤-suc ℓ≤Λ refl)    (Level.lift a) = bound-unlift ℓ≤Λ a
-- bound-unlift (<₄ ℓ≤Λ) a = {!   !}

-- Properties for Lifiting using Ordering -------------------------------------

module Properties where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  
  unlift-lift-cancel : ∀ (ℓ≤Λ : ℓ ≤ Λ) {A : Set ℓ} → (a : A) → 
    bound-unlift ℓ≤Λ (bound-lift ℓ≤Λ a) ≡ a 
  unlift-lift-cancel (≤-id ℓ)       a = refl  
  unlift-lift-cancel (≤-suc ℓ<Λ refl)    a = unlift-lift-cancel ℓ<Λ a

  lift-unlift-cancel : ∀ (ℓ≤Λ : ℓ ≤ Λ) {A : Set ℓ} → (a : BoundLift ℓ≤Λ A) → 
    bound-lift ℓ≤Λ (bound-unlift ℓ≤Λ a) ≡ a 
  lift-unlift-cancel (≤-id ℓ)              a = refl             
  lift-unlift-cancel (≤-suc ℓ<Λ refl)    (lift a) = cong lift (lift-unlift-cancel ℓ<Λ a)