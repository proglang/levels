
module bar where
  
open import Level
open import Data.List 
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any
open import Relation.Binary.PropositionalEquality 

data _<_ : Level → Level → Set where
  <₁ : ∀ {ℓ} → ℓ < suc ℓ
  <₂ : ∀ {ℓ₁} {ℓ₂} → ℓ₁ < ℓ₂ → ℓ₁ < suc ℓ₂

record _∣ (∣ : Level) : Set ∣ where
  constructor _,ℓ_  
  field 
    ℓ : Level
    ℓ<∣ : ℓ < ∣

[_]_↑ : ∀ {ℓ} (ℓ∣ : ℓ ∣) → Set (suc (_∣.ℓ ℓ∣)) → Set ℓ
[ ℓ ,ℓ <₁ {ℓ}            ] A ↑ = Lift (suc ℓ) A
[ ℓ ,ℓ (<₂ {_} {ℓ₂} ℓ<∣) ] A ↑ = Lift {a = ℓ₂} _ ([ ℓ ,ℓ ℓ<∣ ] A ↑)

[_]_↓ :  ∀ {ℓ} (ℓ∣ : ℓ ∣) → [ ℓ∣ ] Set (_∣.ℓ ℓ∣) ↑ → Set (_∣.ℓ ℓ∣)
[ _ ,ℓ <₁     ] lift A ↓ = A
[ ℓ ,ℓ <₂ ℓ<∣ ] lift A ↓ = [ ℓ ,ℓ ℓ<∣ ] A ↓

Env = List Level

⨆_ : Env → Level
⨆ []       = zero
⨆ (ℓ ∷ ℓs) = suc ℓ ⊔ ⨆ ℓs

⟦_⟧η : (Δ : Env) → Set (⨆ Δ)
⟦ Δ ⟧η = ∀ (ℓ∣ : (⨆ Δ) ∣) → ℓ ℓ∣ ∈ Δ → [ ℓ∣ ] Set (ℓ ℓ∣) ↑
  where open _∣

data Type (Δ : Env) : Level → Set where
  ‵ℕ    : Type Δ zero
  ‵_    : ∀ {ℓ} → ℓ ∈ Δ → Type Δ ℓ
  _‵⇒_  : ∀ {ℓ₁ ℓ₂} → Type Δ ℓ₁ → Type Δ ℓ₂ → Type Δ (ℓ₁ ⊔ ℓ₂)
  ‵∀[_] : ∀ {ℓ ℓ′} → Type (ℓ ∷ Δ) ℓ′ → Type Δ (suc ℓ ⊔ ℓ′)

pattern ‵∀_⇒_ ℓ {ℓ′ = ℓ′} T = ‵∀[_] {ℓ = ℓ} {ℓ′ = ℓ′} T

_∷η_ : ∀ {ℓ} {Δ : Env} → Set ℓ → ⟦ Δ ⟧η → ⟦ ℓ ∷ Δ ⟧η
_∷η_ {ℓ} A η (ℓ ,ℓ ℓ<∣) (here refl) = {!   !}
(A ∷η η) (ℓ ,ℓ ℓ<∣) (there x)       = {!   !}

ℓ∈Δ⇒ℓ<⨆Δ : ∀ {ℓ} {Δ : Env} → ℓ ∈ Δ → ℓ < (⨆ Δ)
ℓ∈Δ⇒ℓ<⨆Δ (here refl)             = {! <₁  !}
ℓ∈Δ⇒ℓ<⨆Δ {_} {ℓ′ ∷ ℓs} (there x) = {! (ℓ∈Δ⇒ℓ<⨆Δ x) !}

open import Data.Nat
⟦_⟧_ : ∀{ℓ} {Δ : Env} → (T : Type Δ ℓ) → ⟦ Δ ⟧η → Set ℓ
⟦ ‵ℕ       ⟧ η = ℕ
⟦ ‵ α      ⟧ η = [ _ ,ℓ (ℓ∈Δ⇒ℓ<⨆Δ α) ] η _ α ↓
⟦ T₁ ‵⇒ T₂ ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η  
⟦ ‵∀[ T ]  ⟧ η = ∀ ⟦α⟧ → ⟦ T ⟧ (⟦α⟧ ∷η η) 