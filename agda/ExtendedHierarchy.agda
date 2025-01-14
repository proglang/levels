module ExtendedHierarchy where

open import Level using (Level; zero; suc; _⊔_; Setω)

Setε₀ = Setω

infix 40 ω↑_+_
-- should be a private postulate but we keep it public
-- so we can prove level equalities that would in normally be solved by the compiler
postulate
  ω↑_+_ : (ℓ₁ ℓ₂ : Level) → Level

postulate
  β-suc-zero : suc zero ≡ ω↑ zero + zero
  β-suc-ω    : suc (ω↑ ℓ₁ + ℓ₂) ≡ ω↑ ℓ₁ + suc ℓ₂

  distributivity : ω↑ ℓ + (ℓ₁ ⊔ ℓ₂) ≡ ω↑ ℓ + ℓ₁ ⊔ ω↑ ℓ + ℓ₂ 

  subsumption₁₀ : ℓ ⊔ ω↑ ℓ₁ + ℓ ≡ ω↑ ℓ₁ + ℓ
  subsumption₁₁ : ℓ ⊔ ω↑ ℓ₁ + suc ℓ ≡ ω↑ ℓ₁ + suc ℓ
  subsumption₁₂ : ℓ ⊔ ω↑ ℓ₁ + suc (suc ℓ) ≡ ω↑ ℓ₁ + suc (suc ℓ)

  subsumption₂₀ : ℓ ⊔ ω↑ ℓ₁ + ω↑ ℓ₂ + ℓ ≡ ω↑ ℓ₁ + ω↑ ℓ₂ + ℓ
  subsumption₂₁ : ℓ ⊔ ω↑ ℓ₁ + ω↑ ℓ₂ + suc ℓ ≡ ω↑ ℓ₁ + ω↑ ℓ₂ + suc ℓ
  subsumption₂₂ : ℓ ⊔ ω↑ ℓ₁ + ω↑ ℓ₂ + suc (suc ℓ) ≡ ω↑ ℓ₁ + ω↑ ℓ₂ + suc (suc ℓ)

    -- ...
  
postulate
  -- by definition
  ↑_       : (ℓ : Level) → Level
  β-↑-zero : ↑ zero ≡ zero
  -- note: β-↑-suc must not defined: apply β-suc-0 and β-suc-ω manually then use β-↑-ω
  --       β-↑-suc : ↑ (suc ℓ) ≡ ↑ ℓ
  β-↑-ω    : ↑ (ω↑ ℓ₁ + ℓ₂) ≡ ℓ₁  


open import Ordinal public
#_ : MutualOrd → Level
# 𝟎                = zero
# ω^ l₁ + l₂ [ _ ] = ω↑ # l₁ + # l₂