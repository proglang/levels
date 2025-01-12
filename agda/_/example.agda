open import Level using (zero; suc; Level; Level[_]; _⊔_; _<_)
open import Data.List using ([]; _∷_; List) 
open import Data.List.Membership.Propositional using (∈)

Env : Set
Env = List Level

variable 
  ℓ : Level
  Δ : Env

Δℓ : Env → Level
Δℓ []      = zero
Δℓ (ℓ ∷ Δ) = suc ℓ ⊔ Δℓ Δ

⟦_⟧Δ : (Δ : Env) → Set (Δℓ Δ)
⟦ Δ ⟧Δ = ∀ (ℓ : Level[ Δℓ Δ ]) → ℓ ∈ Δ → Set ℓ
-- Behaves like ∀ (ℓ : Level) {ℓ < Δℓ Δ} → ℓ ∈ Δ → Set ℓ

∅Δ : ⟦ [] ⟧Δ
∅Δ _ ()

postulate
  subsumption : x < y → x < (y ⊔ z)

ℓ∈Δ→ℓ<Δℓ : ℓ ∈ Δ → ℓ < Δℓ Δ
ℓ∈Δ→ℓ<Δℓ (here refl) = ? -- follows by subsumption
ℓ∈Δ→ℓ<Δℓ (there x)   = ? -- follows by subsumption

_∷Δ_ : Set ℓ → ⟦ Δ ⟧Δ → ⟦ ℓ ∷ Δ ⟧Δ
(A ∷Δ Δ) ℓ {<ℓ} (here refl) = A   
(A ∷Δ Δ) ℓ {<ℓ} (there x)   = Δ   
