{-# OPTIONS --rewriting --confluence-check #-}

module ExtendedLevels where

open import Level renaming (Setω to Setε₀) public 
open import Agda.Builtin.Equality
open import Data.Sum.Base

infix 40 ω↑_+_
-- this should be private postulate
-- and only the safe wrapper should be used
-- but for convenience we leave this public for proving 
-- casting equalities (see below)
-- they become obsolete once the compiler solves all equations  
postulate
  ω↑_+_ : (ℓ₁ ℓ₂ : Level) → Level

cast : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≡ ℓ₂ → Set ℓ₁ → Set ℓ₂ 
cast refl A = A


private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

postulate
  -- by definition
  β-suc-zero : suc zero ≡ ω↑ zero + zero
  β-suc-ω    : suc (ω↑ ℓ₁ + ℓ₂) ≡ ω↑ ℓ₁ + suc ℓ₂
  
  -- proved in separate fuile
  distributivity : ω↑ ℓ + (ℓ₁ ⊔ ℓ₂) ≡ ω↑ ℓ + ℓ₁ ⊔ ω↑ ℓ + ℓ₂ 
  
  subsumption₁₀ : ℓ ⊔ ω↑ ℓ₁ + ℓ ≡ ω↑ ℓ₁ + ℓ
  subsumption₁₁ : ℓ ⊔ ω↑ ℓ₁ + suc ℓ ≡ ω↑ ℓ₁ + suc ℓ
  subsumption₁₂ : ℓ ⊔ ω↑ ℓ₁ + suc (suc ℓ) ≡ ω↑ ℓ₁ + suc (suc ℓ)
  
  subsumption₂₀ : ℓ ⊔ ω↑ ℓ₁ + ω↑ ℓ₂ + ℓ ≡ ω↑ ℓ₁ + ω↑ ℓ₂ + ℓ
  subsumption₂₁ : ℓ ⊔ ω↑ ℓ₁ + ω↑ ℓ₂ + suc ℓ ≡ ω↑ ℓ₁ + ω↑ ℓ₂ + suc ℓ
  subsumption₂₂ : ℓ ⊔ ω↑ ℓ₁ + ω↑ ℓ₂ + suc (suc ℓ) ≡ ω↑ ℓ₁ + ω↑ ℓ₂ + suc (suc ℓ)

  -- ...

-- cannot add these rewrite rule, even though they appear be legal >.>
-- {-# REWRITE  β-suc-0 β-suc-ω distributivity #-}

postulate
  -- by definition
  ↑_    : (ℓ : Level) → Level
  β-↑-0   : ↑ zero ≡ zero
  -- β-↑-suc must not defined: apply β-suc-0 and β-suc-ω manually then use β-↑-ω
  -- β-↑-suc : ↑ (suc ℓ) ≡ ↑ ℓ
  β-↑-ω   : ↑ (ω↑ ℓ₁ + ℓ₂) ≡ ℓ₁  

open import Agda.Builtin.Equality.Rewrite
{-# REWRITE β-↑-0 β-↑-ω #-}

infix  30 _<_ _≤_ _>_ _≥_
data _<_ : Level → Level → Set where
 <₁ : zero < ω↑ ℓ₁ + ℓ₂
 <₂ : ℓ₁ < ℓ₃ → ω↑ ℓ₁ + ℓ₂ < ω↑ ℓ₃ + ℓ₄
 <₃ : ℓ₁ ≡ ℓ₃ → ℓ₂ < ℓ₄ → ω↑ ℓ₁ + ℓ₂ < ω↑ ℓ₃ + ℓ₄

_>_ _≥_ _≤_ : Level → Level → Set
a > b = b < a
a ≥ b = a > b ⊎ (a ≡ b)
a ≤ b = b ≥ a

data WellFormed : Level → Set where
  ⊢zero : WellFormed zero
  ⊢ω    : WellFormed ℓ₁ → WellFormed ℓ₂ → ℓ₁ ≥ (↑ ℓ₂) → WellFormed (ω↑ ℓ₁ + ℓ₂)

-- safe wrapper around ω↑_+_
ω↑_+_[_] : (ℓ₁ ℓ₂ : Level) → WellFormed (ω↑ ℓ₁ + ℓ₂) → Level
ω↑_+_[_] ℓ₁ ℓ₂ _ = ω↑ ℓ₁ + ℓ₂

postulate
  -- proved in separate file
  ℓ≥zero : ℓ ≥ zero

ℓ≥ℓ : ℓ ≥ ℓ 
ℓ≥ℓ = inj₂ refl
  
ω↑ : (ℓ : Level) → WellFormed ℓ → Level
ω↑ ℓ ⊢ℓ = ω↑ ℓ + zero [ ⊢ω ⊢ℓ ⊢zero ℓ≥zero ]

one ω : Level
one = ω↑ zero ⊢zero
ω   = ω↑ one (⊢ω ⊢zero ⊢zero ℓ≥ℓ)

⊢one : WellFormed one
⊢one = ⊢ω ⊢zero ⊢zero ℓ≥ℓ

postulate
  -- provable
  lemma : (ℓ : Level) → ℓ < ω → ℓ′ ≥ (↑ ℓ)

ω+_[_,_] : (ℓ : Level) → WellFormed ℓ → ℓ < ω → Level
ω+ ℓ [ ⊢ℓ , ℓ<ω ] = ω↑ one + ℓ [ ⊢ω ⊢one ⊢ℓ (lemma ℓ ℓ<ω) ]

ω+1 : Level
ω+1 = ω+ one [ ⊢one , <₂ {ℓ₂ = zero} {ℓ₄ = zero} (<₁ {ℓ₁ = zero} {ℓ₂ = zero}) ]  