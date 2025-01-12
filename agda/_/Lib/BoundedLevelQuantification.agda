module Code.BoundedLevelQuantification where

open import Level hiding (Lift; lift)

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Level
  Λ Λ′ Λ₁ Λ₂ Λ₃ : Level

module Ordering where
  data _<_ : Level → Level → Set where
    <₁ : ℓ < suc ℓ
    <₂ : ℓ₁ < ℓ₂ → ℓ₁ < suc ℓ₂
    <₃ : ℓ < ℓ₁ → ℓ < (ℓ₁ ⊔ ℓ₂)

open Ordering public

record Level[_] (Λ : Level) : Set Λ where
  constructor _,_  
  field 
    level : Level
    ℓ<Λ : level < Λ

open Level[_] public

bound : Level[ Λ ] → Level
bound {Λ} _ = Λ

Lift  : ∀ (l : Level[ Λ ]) → Set (suc (level l)) → Set Λ
Lift (ℓ , <₁)                         A = Level.Lift (suc ℓ) A
Lift (ℓ , <₂ {ℓ₂ = ℓ₂} ℓ<Λ)           A = Level.Lift {a = ℓ₂} _ (Lift (ℓ , ℓ<Λ) A)
Lift (ℓ , <₃ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} ℓ<Λ) A = Level.Lift {a = ℓ₁} ℓ₂ (Lift (ℓ , ℓ<Λ) A)

lift : ∀ (l : Level[ Λ ]) → Set (level l) → Lift l (Set (level l))
lift (level , <₁)     A = Level.lift A
lift (level , <₂ ℓ<Λ) A = Level.lift (lift (level , ℓ<Λ) A)
lift (level , <₃ ℓ<Λ) A = Level.lift (lift (level , ℓ<Λ) A)

unlift : ∀ (l : Level[ Λ ]) → Lift l (Set (level l)) → Set (level l)
unlift (level , <₁)     (Level.lift A) = A
unlift (level , <₂ ℓ<Λ) (Level.lift A) = unlift ((level , ℓ<Λ)) A
unlift (level , <₃ ℓ<Λ) (Level.lift A) = unlift ((level , ℓ<Λ)) A

module Properties where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  
  inverse-property : ∀ (l : Level[ Λ ]) (A : Set (level l)) → unlift l (lift l A) ≡ A 
  inverse-property (ℓ , <₁)     A = refl
  inverse-property (ℓ , <₂ ℓ<Λ) A = inverse-property (ℓ , ℓ<Λ) A
  inverse-property (ℓ , <₃ ℓ<Λ) A = inverse-property (ℓ , ℓ<Λ) A