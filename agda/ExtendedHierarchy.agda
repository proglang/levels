{-# OPTIONS --warn=noUserWarning #-}
open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; trans; subst; dsubst₂)
open import Level

--! L >

-- Extended hierarchy ---------------------------------------------------------

infix 40 ω^_+_
postulate
--! Cantor
  ω^_+_ : (ℓ₁ ℓ₂ : Level) → Level

{-# WARNING_ON_USAGE ω^_+_ "Safety: check that constructed levels do not violate the order invariant of cantor normal form" #-}

-- with symbols for valid ordinals in cnf our hierarchy grows to ε₀
Setε₀ = Setω

-- safe interface for constructing infinite levels that fulfill the cnf invariant
open import Ordinal public
--! toLevel
⌊_⌋ : MutualOrd → Level
⌊ 𝟎 ⌋                = zero
⌊ ω^ l₁ + l₂ [ _ ] ⌋ = ω^ ⌊ l₁ ⌋ + ⌊ l₂ ⌋

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  
postulate
  -- compiler laws to solve level (in-)equalities
  -- the laws are proven below for the mutual ord representation
--! Axioms
  β-suc-zero         : suc zero ≡ ω^ zero + zero         -- definitional
  β-suc-ω            : suc (ω^ ℓ₁ + ℓ₂) ≡ ω^ ℓ₁ + suc ℓ₂ -- definitional
  distributivity     : ω^ ℓ + (ℓ₁ ⊔ ℓ₂) ≡ ω^ ℓ + ℓ₁ ⊔ ω^ ℓ + ℓ₂
  subsumption-add₁₀  : ℓ ⊔ ω^ ℓ₁ + ℓ ≡ ω^ ℓ₁ + ℓ
  subsumption-exp₁₀  : ℓ ⊔ ω^ ℓ + ℓ₁ ≡ ω^ ℓ + ℓ₁

  -- in reality Agda would apply an infinite set of equations:
  --   subsumption-addₙₘ for all n, m ∈ ℕ
  --   subsumption-expₙₘ for all n, m ∈ ℕ
  -- or more specifically:
  --   subsumption : ℓ ⊔ ω^ ℓ₁ + ℓ ≡ ω^ ℓ₁ + ℓ₂ if ℓ occurs in ℓ₁ or ℓ₂
  --
  -- note on solving strategy:
  --   using β-suc-zero and β-suc-ω, suc is always pushed inside the ordinal 
  --   then the distributivity and the subsumption laws can be applied
  --   otherwise the already existing laws in Agda's compiler will reduce further:
  ---    https://agda.readthedocs.io/en/latest/language/universe-levels.html#intrinsic-level-properties
  --
  -- conjecture: this rewriting system is complete, confluent and terminating

-- Casting Set Levels ---------------------------------------------------------

--! cast {
cast : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≡ ℓ₂ → Set ℓ₁ → Set ℓ₂ 
cast refl A = A

cast-intro : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} → (eq : ℓ₁ ≡ ℓ₂) → A → cast eq A  
cast-intro refl a = a

cast-elim : ∀ {ℓ₁ ℓ₂} → (eq : ℓ₁ ≡ ℓ₂) → {A : Set ℓ₁} → cast eq A → A  
cast-elim refl a = a
--! }

dsubst : ∀{ℓ}{A : Set ℓ} (f : A → Level) (P : ∀ a → Set (f a)) {x y : A} → x ≡ y → P x → P y
dsubst f P refl px = px

cast' : ℓ₁ ≡ ℓ₂ → Set ℓ₁ → Set ℓ₂
cast' eq A = dsubst _ (λ ℓ → Set ℓ) eq A

cast-elim-intro-cancel : ∀ {ℓ₁ ℓ₂} → (eq : ℓ₁ ≡ ℓ₂) → {A : Set ℓ₁} → (a : A) → cast-elim eq (cast-intro eq a) ≡ a  
cast-elim-intro-cancel refl a = refl

cast-intro-elim-cancel : ∀ {ℓ₁ ℓ₂} → (eq : ℓ₁ ≡ ℓ₂) → {A : Set ℓ₁} → (a : cast eq A) → cast-intro eq (cast-elim eq a) ≡ a 
cast-intro-elim-cancel refl a = refl

-- MutualOrd Instantiations ---------------------------------------------------

open import Data.Sum using (_⊎_; inj₁; inj₂) 

ω^⟨_⟩ : MutualOrd → MutualOrd
ω^⟨ a ⟩ = ω^ a + 𝟎 [ ≥𝟎 ]

𝟏 ω ω+1 ω+2 : MutualOrd
𝟏 = ω^⟨ 𝟎 ⟩
𝟐 = ω^ 𝟎 + 𝟏 [ inj₂ refl ]
ω = ω^⟨ 𝟏 ⟩
ω² = ω^⟨ 𝟐 ⟩
ω+1 = ω^ 𝟏 + 𝟏 [ inj₁ <₁ ]
ω+2 = ω^ 𝟏 + 𝟐 [ inj₁ <₁ ]

-- Successor & Maximum Operation on MutualOrd ---------------------------------

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; subst; subst₂) 
  renaming (sym to _⁻¹; trans to _∙_)

sucₒ : MutualOrd → MutualOrd
fst-ignores-suc : ∀ a → (fst a) ≡ fst (sucₒ a)

sucₒ 𝟎 = 𝟏
sucₒ ω^ a + b [ r ] = ω^ a + sucₒ b [ subst (a ≥_) (fst-ignores-suc b) r ]

fst-ignores-suc 𝟎              = refl
fst-ignores-suc ω^ a + b [ r ] = refl
  
_⊔ₒ_ : MutualOrd → MutualOrd → MutualOrd
𝟎 ⊔ₒ              a              = a
a              ⊔ₒ 𝟎              = a
ω^ a + b [ r ] ⊔ₒ ω^ c + d [ s ] with <-tri a c 
... | inj₁ _        = ω^ c + d [ s ]
... | inj₂ (inj₁ _) = ω^ a + b [ r ]
... | inj₂ (inj₂ _) with <-tri b d 
... | inj₁ _        = ω^ c + d [ s ]
... | inj₂ (inj₁ _) = ω^ a + b [ r ]
... | inj₂ (inj₂ _) = ω^ c + d [ s ]

-- Interaction between the Level and MutualOrd Representation -----------------

β-suc-⌊⌋ : ∀ {a} → suc ⌊ a ⌋ ≡ ⌊ sucₒ a ⌋
β-suc-⌊⌋ {𝟎} = β-suc-zero
β-suc-⌊⌋ {ω^ a + b [ r ]} =  subst (λ x → suc (ω^ ⌊ a ⌋ + ⌊ b ⌋) ≡ ω^ ⌊ a ⌋ + x)
  (β-suc-⌊⌋ {b}) (β-suc-ω {⌊ a ⌋} {⌊ b ⌋}) 

-- Translation between ℕ and MutualOrd Representations ------------------------

open import Data.Nat using (ℕ)

ℕ→MutualOrd : ℕ → MutualOrd
ℕ→MutualOrd ℕ.zero    = 𝟎
ℕ→MutualOrd (ℕ.suc n) = sucₒ (ℕ→MutualOrd n)

fst[a]≡0→a<ω : ∀ a → fst a ≡ 𝟎 → a < ω
fst[a]≡0→a<ω 𝟎 eq                = <₁
fst[a]≡0→a<ω ω^ a + b [ r ] refl = <₂ <₁

MutualOrd→ℕ : (a : MutualOrd) → a < ω → ℕ
MutualOrd→ℕ a <₁ = ℕ.zero
MutualOrd→ℕ a (<₂ {b = b} {inj₂ y} <₁) = ℕ.suc (MutualOrd→ℕ b (fst[a]≡0→a<ω b (y ⁻¹)))

fst[ℕ→MutualOrd]≡0 : ∀ n → fst (ℕ→MutualOrd n) ≡ 𝟎
fst[ℕ→MutualOrd]≡0 ℕ.zero    = refl
fst[ℕ→MutualOrd]≡0 (ℕ.suc n) = 
    (fst-ignores-suc (ℕ→MutualOrd n) ⁻¹) ∙ (fst[ℕ→MutualOrd]≡0 n)

ω+ₙ_ : ℕ → MutualOrd
ω+ₙ n = ω^ 𝟏 + ℕ→MutualOrd n [ subst (𝟏 ≥_) (fst[ℕ→MutualOrd]≡0 n ⁻¹) (inj₁ <₁) ]

-- Properties for Successor and Maximum Operation ------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

distributivity′ : ∀ (a b c : MutualOrd) 
                  (r : a ≥ fst (b ⊔ₒ c)) (s : a ≥ fst b) (t : a ≥ fst c) → 
  ω^ a + (b ⊔ₒ c) [ r ] ≡ ω^ a + b [ s ] ⊔ₒ ω^ a + c [ t ]
distributivity′ a b c r s t with <-tri a a
... | inj₁ a<a = ⊥-elim (<-irrefl a<a)
... | inj₂ (inj₁ a<a) = ⊥-elim (<-irrefl a<a)
distributivity′ a 𝟎 𝟎 r s t | inj₂ (inj₂ refl) = MutualOrd⁼ refl refl
distributivity′ a 𝟎 ω^ c + c₁ [ x ] r s t | inj₂ (inj₂ refl) = MutualOrd⁼ refl refl
distributivity′ a ω^ b + b₁ [ x ] 𝟎 r s t | inj₂ (inj₂ refl) = MutualOrd⁼ refl refl
distributivity′ a ω^ ba + bb [ br ] ω^ ca + cb [ ct ] r s t | inj₂ (inj₂ refl) 
  with <-tri ba ca 
... | inj₁ _ = MutualOrd⁼ refl refl
... | inj₂ (inj₁ _) = MutualOrd⁼ refl refl
... | inj₂ (inj₂ refl) with <-tri bb cb 
... | inj₁ _ = MutualOrd⁼ refl refl
... | inj₂ (inj₁ _) = MutualOrd⁼ refl refl
... | inj₂ (inj₂ _) = MutualOrd⁼ refl refl

right-id′  : ∀ a → (a ⊔ₒ 𝟎) ≡ a
right-id′  𝟎 = refl
right-id′  ω^ a + a₁ [ x ] = refl

idem′ : ∀ a → (a ⊔ₒ a) ≡ a
idem′ 𝟎 = refl
idem′ ω^ a + b [ r ] with <-tri a a 
... | inj₁ a<a = ⊥-elim (<-irrefl a<a)
... | inj₂ (inj₁ a<a) = ⊥-elim (<-irrefl a<a)
... | inj₂ (inj₂ refl) with <-tri b b 
... | inj₁ a<a = ⊥-elim (<-irrefl a<a)
... | inj₂ (inj₁ a<a) = ⊥-elim (<-irrefl a<a)
... | inj₂ (inj₂ refl) = refl

¬ω^a+b<b : ∀ {a b : MutualOrd} {r : a ≥ fst b} → ¬ (ω^ a + b [ r ] < b)
¬ω^a+b<b {r = r} (<₂ a<c) = ⊥-elim (Lm[≥→¬<] r a<c)
¬ω^a+b<b (<₃ refl x)      = ⊥-elim (¬ω^a+b<b x)

subsumption-add₁₀′ : ∀ (a b : MutualOrd) (s : a ≥ fst b) → 
  b ⊔ₒ ω^ a + b [ s ] ≡ ω^ a + b [ s ]
subsumption-add₁₀′ a 𝟎              s = refl 
subsumption-add₁₀′ a ω^ b + d [ r ] s with <-tri b a 
... | inj₁ _          = refl
... | inj₂ (inj₁ a<b) = ⊥-elim (Lm[≥→¬<] s a<b)
... | inj₂ (inj₂ refl) with <-tri d ω^ b + d [ r ]
... | inj₁ _ = refl
... | inj₂ (inj₁ ω^b+d<d) = (⊥-elim (¬ω^a+b<b ω^b+d<d)) 

¬ω^a+b<a : ∀ {a b : MutualOrd} {r : a ≥ fst b} → ¬ (ω^ a + b [ r ] < a)
¬ω^a+b<a (<₂ x) = ⊥-elim (¬ω^a+b<a x)

subsumption-exp₁₀′ : ∀ (a b : MutualOrd) (s : a ≥ fst b) → 
  a ⊔ₒ ω^ a + b [ s ] ≡ ω^ a + b [ s ]
subsumption-exp₁₀′ 𝟎                b s = refl 
subsumption-exp₁₀′ ω^ aa + ab [ r ] b s with <-tri aa (ω^ aa + ab [ r ])
... | inj₁ x = refl
... | inj₂ (inj₁ x) = ⊥-elim (¬ω^a+b<a x)

-- Type Theoretic Ordinal Property --------------------------------------------

open import Universe using (module Lib; module IRUniverse)
open Lib
open IRUniverse
open import Function using (flip)

lvl : LvlStruct
lvl = record {
    Lvl    = MutualOrd
  ; _<_    = _<_
  ; <-prop = <IsPropValued _ _
  ; _∘_    = flip <-trans
  ; wf     = WF _
  }
    
open IR-Universe lvl hiding (_<_)
  
<-extensional : {a b : MutualOrd} → 
  ((c : MutualOrd) → (c < a → c < b) × (c < b → c < a)) → 
  a ≡ b
<-extensional {a} {b} f with <-tri a b | f a | f b 
... | inj₁ a<b         | _ , a<b→a<a | _ , _ = ⊥-elim (<-irrefl (a<b→a<a a<b))
... | inj₂ (inj₁ b<a)  | _ , _ | b<a→b<b , _ = ⊥-elim (<-irrefl (b<a→b<b b<a))
... | inj₂ (inj₂ refl) | _ , _ | _ , _       = refl
  
ord : Ordinal lvl
ord = record { 
    cmp   = <-tri 
  ; <-ext = <-extensional 
  }  
       
open IR-Univ-Ordinal ord           
