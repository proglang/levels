{-# OPTIONS --rewriting --no-load-primitives --confluence-check #-}

module Prelude where

-- Agda.Primitive
{-# BUILTIN PROP           Prop      #-}
{-# BUILTIN TYPE           Set       #-}
{-# BUILTIN STRICTSET      SSet      #-}
{-# BUILTIN PROPOMEGA      Propε₀    #-}
{-# BUILTIN SETOMEGA       Setε₀     #-}
{-# BUILTIN STRICTSETOMEGA SSetε₀    #-}
{-# BUILTIN LEVELUNIV      LevelUniv #-}

postulate
  Level : LevelUniv

{-# BUILTIN LEVEL Level #-}

postulate
  zero  : Level
  suc   : (ℓ : Level) → Level
  _⊔_   : (ℓ₁ ℓ₂ : Level) → Level

infixl 6 _⊔_

{-# BUILTIN LEVELZERO zero #-}
{-# BUILTIN LEVELSUC  suc  #-}
{-# BUILTIN LEVELMAX  _⊔_  #-}

infix 40 ω↑_+_
-- this should be private postulate
-- and only the safe wrapper should be used
-- but for convenience we leave this public for proving 
-- casting equalities (see below)
-- they become obsolete once the compiler solves all equations  
postulate
  ω↑_+_ : (ℓ₁ ℓ₂ : Level) → Level

-- Agda.Primitive.Cubical
-- {-# BUILTIN CUBEINTERVALUNIV IUniv #-}  -- IUniv : SSet₁
-- {-# BUILTIN INTERVAL I  #-}  -- I : IUniv
-- 
-- {-# BUILTIN IZERO    i0 #-}
-- {-# BUILTIN IONE     i1 #-}
-- 
-- -- I is treated as the type of booleans.
-- {-# COMPILE JS i0 = false #-}
-- {-# COMPILE JS i1 = true  #-}
-- 
-- infix  30 primINeg
-- infixr 20 primIMin primIMax
-- 
-- primitive
--     primIMin : I → I → I
--     primIMax : I → I → I
--     primINeg : I → I
-- 
-- {-# BUILTIN ISONE    IsOne    #-} 
-- 
-- postulate
--   itIsOne : IsOne i1
--   IsOne1  : ∀ i j → IsOne i → IsOne (primIMax i j)
--   IsOne2  : ∀ i j → IsOne j → IsOne (primIMax i j)
-- 
-- {-# BUILTIN ITISONE  itIsOne  #-}
-- {-# BUILTIN ISONE1   IsOne1   #-}
-- {-# BUILTIN ISONE2   IsOne2   #-}
-- 
-- {-# COMPILE JS itIsOne = { "tt" : a => a["tt"]() } #-}
-- {-# COMPILE JS IsOne1 =
--   _ => _ => _ => { return { "tt" : a => a["tt"]() } }
--   #-}
-- {-# COMPILE JS IsOne2 =
--   _ => _ => _ => { return { "tt" : a => a["tt"]() } }
--   #-}
-- 
-- {-# BUILTIN PARTIAL  Partial  #-}
-- {-# BUILTIN PARTIALP PartialP #-}
-- 
-- postulate
--   isOneEmpty : ∀ {ℓ} {A : Partial i0 (Set ℓ)} → PartialP i0 A
-- 
-- {-# BUILTIN ISONEEMPTY isOneEmpty #-}
-- 
-- {-# COMPILE JS isOneEmpty =
--   _ => x => _ => x({ "tt" : a => a["tt"]() })
--   #-}
-- 
-- primitive
--   primPOr : ∀ {ℓ} (i j : I) {A : Partial (primIMax i j) (Set ℓ)}
--             → (u : PartialP i (λ z → A (IsOne1 i j z)))
--             → (v : PartialP j (λ z → A (IsOne2 i j z)))
--             → PartialP (primIMax i j) A
-- 
--   primComp : ∀ {ℓ} (A : (i : I) → Set (ℓ i)) {φ : I} (u : ∀ i → Partial φ (A i)) (a : A i0) → A i1
-- 
-- syntax primPOr p q u t = [ p ↦ u , q ↦ t ]
-- 
-- primitive
--   primTransp : ∀ {ℓ} (A : (i : I) → Set (ℓ i)) (φ : I) (a : A i0) → A i1
--   primHComp  : ∀ {ℓ} {A : Set ℓ} {φ : I} (u : ∀ i → Partial φ A) (a : A) → A
-- 
-- 
-- postulate
--   PathP : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
-- 
-- {-# BUILTIN PATHP        PathP     #-}
  
-- Agda.Builtin.Equality
infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

subst : ∀ {ℓ} {A : Set ℓ} {x y : A} → x ≡ y → (P : A → Set ℓ) → P x → P y
subst refl P p = p

trans : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cast : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≡ ℓ₂ → Set ℓ₁ → Set ℓ₂ 
cast refl A = A

-- Agda.Builtin.Equality.Rewrite
{-# BUILTIN REWRITE _≡_ #-}

-- Level
record Lift {a} ℓ (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field lower : A

open Lift public

-- Data.Sum.Base
data _⊎_ {a} {b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

-- Level extensions
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

-- cannot add these rewrite rule, even though they appear be legal >.>
-- {-# REWRITE  β-suc-0 β-suc-ω distributivity #-}

postulate
  -- by definition
  ↑_    : (ℓ : Level) → Level
  β-↑-0   : ↑ zero ≡ zero
  -- β-↑-suc not defined apply manually β-suc-0 and β-suc-ω first
  β-↑-ω   : ↑ (ω↑ ℓ₁ + ℓ₂) ≡ ℓ₁  

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