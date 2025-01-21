module BoundQuantification where


open import Level
open import Agda.Builtin.Equality using (refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
  

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  Λ Λ′ Λ₁ Λ₂ Λ₃ Λ₄ : Level

-- ordering on levels 
data _≤_ : Level → Level → Set where
  <₁ : ℓ ≤ ℓ
  <₂ : ℓ₁ ≤ ℓ₂ → ℓ₁ ≤ suc ℓ₂
  <₃ : ℓ ≤ ℓ₁ → ℓ ≤ (ℓ₁ ⊔ ℓ₂)

_<_ : Level → Level → Set
_<_ ℓ₁ ℓ₂ = suc ℓ₁ ≤ ℓ₂ 

-- a bound level is a level `#` along a proof that `#` is smaller than the bound on the level `Λ`
record BoundLevel (Λ : Level) : Set where
  constructor _,_  
  field 
    # : Level
    #<Λ : # < Λ

open BoundLevel public

bound : BoundLevel Λ → Level
bound {Λ} _ = Λ

BoundLift  : ℓ ≤ Λ → Set ℓ → Set Λ
BoundLift {ℓ} <₁                 A = Lift ℓ A
BoundLift {ℓ} (<₂ {ℓ₂ = ℓ₂} ℓ≤Λ) A = Lift (suc ℓ₂) (BoundLift ℓ≤Λ A)
BoundLift {ℓ} (<₃ {ℓ₂ = ℓ₂} ℓ≤Λ) A = Lift ℓ₂ (BoundLift ℓ≤Λ A)

bound-lift : ∀ (ℓ≤Λ : ℓ ≤ Λ) → {A : Set ℓ} → A → BoundLift ℓ≤Λ A
bound-lift {ℓ} <₁       a = lift a
bound-lift {ℓ} (<₂ ℓ≤Λ) a = lift (bound-lift ℓ≤Λ a)
bound-lift {ℓ} (<₃ ℓ≤Λ) a = lift (bound-lift ℓ≤Λ a)

bound-unlift : ∀ (ℓ≤Λ : ℓ ≤ Λ) → {A : Set ℓ} → BoundLift ℓ≤Λ A → A
bound-unlift {ℓ} (<₁)     (Level.lift a) = a
bound-unlift {ℓ} (<₂ ℓ≤Λ) (Level.lift a) = bound-unlift ℓ≤Λ a
bound-unlift {ℓ} (<₃ ℓ≤Λ) (Level.lift a) = bound-unlift  ℓ≤Λ a

module Properties where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  
  inverse-property : ∀ (ℓ≤Λ : ℓ ≤ Λ) {A : Set ℓ} → (a : A) → bound-unlift ℓ≤Λ (bound-lift ℓ≤Λ a) ≡ a 
  inverse-property <₁       a = refl
  inverse-property (<₂ ℓ<Λ) a = inverse-property ℓ<Λ a
  inverse-property (<₃ ℓ<Λ) a = inverse-property ℓ<Λ a
