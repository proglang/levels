module BoundQuantification where


open import Level
open import ExtendedHierarchy using (ω^_+_; cast; subsumption₁₀)
open import Agda.Builtin.Equality using (refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
  

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  Λ Λ′ Λ₁ Λ₂ Λ₃ Λ₄ : Level

-- Ordering on Levels ---------------------------------------------------------
data _≤_ : Level → Level → Set where
  <₀ : zero ≤ ℓ
  <₁ : ℓ ≤ ℓ
  <₂ : ℓ₁ ≤ ℓ₂ → ℓ₁ ≤ suc ℓ₂
  <₃ : ℓ ≤ ℓ₁ → ℓ ≤ (ℓ₁ ⊔ ℓ₂)
  <₄ : ℓ ≤ ℓ₁ → ℓ ≤ ω^ ℓ₂ + ℓ₁

_<_ : Level → Level → Set
_<_ ℓ₁ ℓ₂ = suc ℓ₁ ≤ ℓ₂ 

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
BoundLift {ℓ} {Λ} <₀             A = Lift Λ A
BoundLift {ℓ} <₁                 A = Lift ℓ A
BoundLift {ℓ} (<₂ {ℓ₂ = ℓ₂} ℓ≤Λ) A = Lift (suc ℓ₂) (BoundLift ℓ≤Λ A)
BoundLift {ℓ} (<₃ {ℓ₂ = ℓ₂} ℓ≤Λ) A = Lift ℓ₂ (BoundLift ℓ≤Λ A)
BoundLift (<₄ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} ℓ≤Λ) A = 
  cast (subsumption₁₀ {ℓ = ℓ₁} {ℓ₁ = ℓ₂}) (Lift (ω^ ℓ₂ + ℓ₁) (BoundLift ℓ≤Λ A))

bound-lift : ∀ (ℓ≤Λ : ℓ ≤ Λ) → {A : Set ℓ} → A → BoundLift ℓ≤Λ A
bound-lift {ℓ} {Λ} <₀   a = lift a
bound-lift {ℓ} <₁       a = lift a
bound-lift {ℓ} (<₂ ℓ≤Λ) a = lift (bound-lift ℓ≤Λ a)
bound-lift {ℓ} (<₃ ℓ≤Λ) a = lift (bound-lift ℓ≤Λ a)
bound-lift {ℓ} (<₄ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} ℓ≤Λ) a = {!  !}

bound-unlift : ∀ (ℓ≤Λ : ℓ ≤ Λ) → {A : Set ℓ} → BoundLift ℓ≤Λ A → A
bound-unlift (<₀)     (Level.lift a) = a
bound-unlift (<₁)     (Level.lift a) = a
bound-unlift (<₂ ℓ≤Λ) (Level.lift a) = bound-unlift ℓ≤Λ a
bound-unlift (<₃ ℓ≤Λ) (Level.lift a) = bound-unlift  ℓ≤Λ a

-- Properties for Lifiting using Ordering -------------------------------------

module Properties where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  
  unlift-lift-cancel : ∀ (ℓ≤Λ : ℓ ≤ Λ) {A : Set ℓ} → (a : A) → 
    bound-unlift ℓ≤Λ (bound-lift ℓ≤Λ a) ≡ a 
  unlift-lift-cancel <₀       a = refl
  unlift-lift-cancel <₁       a = refl
  unlift-lift-cancel (<₂ ℓ<Λ) a = unlift-lift-cancel ℓ<Λ a
  unlift-lift-cancel (<₃ ℓ<Λ) a = unlift-lift-cancel ℓ<Λ a

  lift-unlift-cancel : ∀ (ℓ≤Λ : ℓ ≤ Λ) {A : Set ℓ} → (a : BoundLift ℓ≤Λ A) → 
    bound-lift ℓ≤Λ (bound-unlift ℓ≤Λ a) ≡ a 
  lift-unlift-cancel <₀       a = refl  
  lift-unlift-cancel <₁       a = refl  
  lift-unlift-cancel (<₂ ℓ<Λ) (lift a) = cong lift (lift-unlift-cancel ℓ<Λ a)
  lift-unlift-cancel (<₃ ℓ<Λ) (lift a) = cong lift (lift-unlift-cancel ℓ<Λ a)  