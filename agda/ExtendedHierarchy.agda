open import Relation.Binary.PropositionalEquality 
  using (_≡_; refl; cong; trans; subst)
open import Level

-- Extended hierarchy ---------------------------------------------------------

infix 40 ω^_+_
postulate
  ω^_+_ : (ℓ₁ ℓ₂ : Level) → Level

-- with symbols for valid ordinals in cnf our hierarchy grows to ε₀
Setε₀ = Setω

-- safe interface for constructing ordinals that fulfill the cnf property
open import Ordinal public
⌊_⌋ : MutualOrd → Level
⌊ 𝟎 ⌋                = zero
⌊ ω^ l₁ + l₂ [ _ ] ⌋ = ω^ ⌊ l₁ ⌋ + ⌊ l₂ ⌋

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  
postulate
  -- compiler laws to solve level (in-)equalities
  -- the laws are in addition to the already given intrinsic level properties 
  -- from the agda stdlib: 
  --  https://agda.readthedocs.io/en/latest/language/universe-levels.html#intrinsic-level-properties
  -- the laws are proven blow at the end of the file 
  β-suc-zero     : suc zero ≡ ω^ zero + zero         -- by definition 
  β-suc-ω        : suc (ω^ ℓ₁ + ℓ₂) ≡ ω^ ℓ₁ + suc ℓ₂ -- by definition
  distributivity : ω^ ℓ + (ℓ₁ ⊔ ℓ₂) ≡ ω^ ℓ + ℓ₁ ⊔ ω^ ℓ + ℓ₂ 
  subsumption₁₀  : ℓ ⊔ ω^ ℓ₁ + ℓ ≡ ω^ ℓ₁ + ℓ
  subsumption₁₁  : ℓ ⊔ ω^ ℓ₁ + suc ℓ ≡ ω^ ℓ₁ + suc ℓ
  subsumption₂₀  : ℓ ⊔ ω^ ℓ₁ + ω^ ℓ₂ + ℓ ≡ ω^ ℓ₁ + ω^ ℓ₂ + ℓ
  subsumption₂₁  : ℓ ⊔ ω^ ℓ₁ + ω^ ℓ₂ + suc ℓ ≡ ω^ ℓ₁ + ω^ ℓ₂ + suc ℓ
  -- in reality the Agda compiler would apply an infinite set of equations:
  -- subsumptionₙₘ for all n, m ∈ ℕ
  -- note on solving strategy:
  -- - using β-suc-zero and β-suc-ω, suc is always pushed inside the ordinal 
  -- - then the distributivity and the subsumption laws can be applied

-- specialized subst for level equality chains
cast : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≡ ℓ₂ → Set ℓ₁ → Set ℓ₂ 
cast refl A = A

-- Example MutualOrd Instanciations -------------------------------------------

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

fst[ℕ→MutualOrd]≡0 : ∀ n → fst (ℕ→MutualOrd n) ≡ 𝟎
fst[ℕ→MutualOrd]≡0 ℕ.zero    = refl
fst[ℕ→MutualOrd]≡0 (ℕ.suc n) = 
    (fst-ignores-suc (ℕ→MutualOrd n) ⁻¹) ∙ (fst[ℕ→MutualOrd]≡0 n)

ω+ₙ_ : ℕ → MutualOrd
ω+ₙ n = ω^ 𝟏 + ℕ→MutualOrd n [ subst (𝟏 ≥_) (fst[ℕ→MutualOrd]≡0 n ⁻¹) (inj₁ <₁) ]

-- Properties for Successor and Maximum Operation ------------------------------

open import Data.Empty using (⊥; ⊥-elim)

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

open import Relation.Nullary using (¬_)

¬ω^a+b<b : ∀ {a b : MutualOrd} {r : a ≥ fst b} → ¬ (ω^ a + b [ r ] < b)
¬ω^a+b<b {r = r} (<₂ a<c) = ⊥-elim (Lm[≥→¬<] r a<c)
¬ω^a+b<b (<₃ refl x)      = ⊥-elim (¬ω^a+b<b x)

subsumption₁₀′ : ∀ (a b : MutualOrd) (s : a ≥ fst b) → 
  b ⊔ₒ ω^ a + b [ s ] ≡ ω^ a + b [ s ]
subsumption₁₀′ a 𝟎              s = refl 
subsumption₁₀′ a ω^ b + d [ r ] s with <-tri b a 
... | inj₁ _          = refl
... | inj₂ (inj₁ a<b) = ⊥-elim (Lm[≥→¬<] s a<b)
... | inj₂ (inj₂ refl) with <-tri d ω^ b + d [ r ]
... | inj₁ _ = refl
... | inj₂ (inj₁ ω^b+d<d) = (⊥-elim (¬ω^a+b<b ω^b+d<d)) 

¬ω^a+suc[b]<b : ∀ {a b : MutualOrd} {r : a ≥ fst (sucₒ b)} → 
  ¬ (ω^ a + sucₒ b [ r ] < b)
¬ω^a+suc[b]<b {r = r} (<₂ a<c) = ⊥-elim (Lm[≥→¬<] r a<c)
¬ω^a+suc[b]<b (<₃ refl x)      = ⊥-elim (¬ω^a+suc[b]<b x)

ω^a+b≡ω^c+d→a≡c :  ∀ {a b c d : MutualOrd} {r : a ≥ fst b} {s : c ≥ fst d} →
   ω^ a + b [ r ] ≡ ω^ c + d [ s ] → a ≡ c
ω^a+b≡ω^c+d→a≡c refl = refl 

ω^a+b≡ω^c+d→b≡d :  ∀ {a b c d : MutualOrd} {r : a ≥ fst b} {s : c ≥ fst d} → 
  ω^ a + b [ r ] ≡ ω^ c + d [ s ] → b ≡ d
ω^a+b≡ω^c+d→b≡d refl = refl 

¬ω^a+suc[b]≡b : ∀ {a b : MutualOrd} {r : a ≥ fst (sucₒ b)} → 
  ¬ (ω^ a + sucₒ b [ r ] ≡ b)
¬ω^a+suc[b]≡b {a} {ω^ b + b₁ [ x₂ ]} {r = inj₁ x₁} x = 
  ⊥-elim (<-irreflexive (ω^a+b≡ω^c+d→a≡c x ⁻¹) x₁)
¬ω^a+suc[b]≡b {.(fst (sucₒ ω^ b + b₁ [ x₁ ]))} {ω^ b + b₁ [ x₁ ]} {r = inj₂ refl} x =
  ⊥-elim (¬ω^a+suc[b]≡b (ω^a+b≡ω^c+d→b≡d x))

subsumption₁₁′ : ∀ (a b : MutualOrd) (s : a ≥ fst (sucₒ b)) → 
  b ⊔ₒ ω^ a + sucₒ b [ s ] ≡ ω^ a + sucₒ b [ s ]
subsumption₁₁′ a 𝟎              s = refl 
subsumption₁₁′ a ω^ b + d [ r ] s with <-tri b a 
... | inj₁ _          = refl
... | inj₂ (inj₁ a<b) = ⊥-elim (Lm[≥→¬<] s a<b)
... | inj₂ (inj₂ refl) 
  with <-tri d (ω^ b + sucₒ d [ subst (λ b₁ → b₁ < b ⊎ b ≡ b₁) (fst-ignores-suc d) r ]) 
... | inj₁ _ = refl
... | inj₂ (inj₁ x) = ⊥-elim (¬ω^a+suc[b]<b x)
... | inj₂ (inj₂ y) = ⊥-elim (¬ω^a+suc[b]≡b (y ⁻¹)) 

-- subsumption₂₀′ : ∀ (a b c : MutualOrd) (r : a ≥ b) (s : b ≥ fst c) → 
--   c ⊔ₒ ω^ a + (ω^ b + c [ s ]) [ r ] ≡ ω^ a + (ω^ b + c [ s ]) [ r ]
-- subsumption₂₀′ a b 𝟎 r s               = refl
-- subsumption₂₀′ a b ω^ ca + cb [ cr ] r s with <-tri ca a 
-- ... | inj₁ _ = refl
-- ... | inj₂ (inj₁ x) = {!   !} --⊥-elim (<-irreflexive (ω^a+b≡ω^c+d→a≡c {!   !}) x)
-- ... | inj₂ (inj₂ refl) with <-tri cb ω^ b + ω^ a + cb [ cr ] [ s ]
-- ... | inj₁ _ = refl
-- ... | inj₂ (inj₁ x) = {!   !} 

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