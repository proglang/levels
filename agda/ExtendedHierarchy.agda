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
  β-suc-zero       : suc zero ≡ ω^ zero + zero         -- definitional
  β-suc-ω          : suc (ω^ ℓ₁ + ℓ₂) ≡ ω^ ℓ₁ + suc ℓ₂ -- definitional
  distributivity   : ω^ ℓ + (ℓ₁ ⊔ ℓ₂) ≡ ω^ ℓ + ℓ₁ ⊔ ω^ ℓ + ℓ₂
  subsumption-add  : ℓ ⊔ ω^ ℓ₁ + ℓ ≡ ω^ ℓ₁ + ℓ
  subsumption-exp  : ℓ ⊔ ω^ ℓ + ℓ₁ ≡ ω^ ℓ + ℓ₁

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

idem′⁼-right : ∀ a b r s → (ω^ a + b [ r ] ⊔ₒ ω^ a + b [ s ]) ≡ ω^ a + b [ s ]
idem′⁼-right a b r s with <-tri a a
... | inj₁ x = refl
... | inj₂ (inj₁ x) = MutualOrd⁼ refl refl
... | inj₂ (inj₂ refl) with <-tri b b 
... | inj₁ x = refl
... | inj₂ (inj₁ x) = MutualOrd⁼ refl refl
... | inj₂ (inj₂ refl) = refl

<-⊔ₒ-left : ∀ a b → b < a → (a ⊔ₒ b) ≡ a
<-⊔ₒ-left a b <₁            = refl
<-⊔ₒ-left ω^ aa + ab [ r ] ω^ ba + bb [ s ] (<₂ x) with <-tri aa ba 
... | inj₁ y = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
... | inj₂ (inj₁ y) = refl 
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ y = ⊥-elim (<-irrefl x) 
... | inj₂ (inj₁ y) = ⊥-elim (<-irrefl x)
... | inj₂ (inj₂ refl) = MutualOrd⁼ refl refl 
<-⊔ₒ-left ω^ aa + ab [ r ] ω^ ba + bb [ s ] (<₃ refl x) with <-tri ba ba 
... | inj₁ y = ⊥-elim (<-irrefl y)
... | inj₂ (inj₁ y) = refl 
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ y = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
... | inj₂ (inj₁ y) = refl
... | inj₂ (inj₂ refl) = MutualOrd⁼ refl refl 

<-⊔ₒ-right : ∀ a b → a < b → (a ⊔ₒ b) ≡ b
<-⊔ₒ-right a b <₁            = refl
<-⊔ₒ-right ω^ aa + ab [ r ] ω^ ba + bb [ s ] (<₂ x) with <-tri aa ba 
... | inj₁ x = refl
... | inj₂ (inj₁ y) = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = refl
... | inj₂ (inj₁ y) = ⊥-elim (<-irrefl x)
... | inj₂ (inj₂ refl) = refl
<-⊔ₒ-right ω^ aa + ab [ r ] ω^ ba + bb [ s ] (<₃ refl x) with <-tri ba ba 
... | inj₁ x = refl
... | inj₂ (inj₁ x) = ⊥-elim (<-irrefl x)
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = refl
... | inj₂ (inj₁ y) = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
... | inj₂ (inj₂ refl) = refl

a<b→a<b⊔c : ∀ a b c → a < b → a < (b ⊔ₒ c)
a<b→a<b⊔c a b 𝟎 a<b = subst (_ <_) (right-id′ _ ⁻¹) a<b
a<b→a<b⊔c a ω^ ba + bb [ br ] ω^ ca + cb [ cr ] a<b with <-tri ba ca
... | inj₁ x = <-trans a<b (<₂ x)
... | inj₂ (inj₁ x) = a<b
... | inj₂ (inj₂ refl) with <-tri bb cb 
... | inj₁ x = <-trans a<b (<₃ refl x)
... | inj₂ (inj₁ x) = a<b
... | inj₂ (inj₂ refl) = subst (a <_) (MutualOrd⁼ refl refl) a<b

assoc′ : ∀ (a b c : MutualOrd) → 
  (a ⊔ₒ b) ⊔ₒ c ≡ a ⊔ₒ (b ⊔ₒ c)
assoc′ 𝟎 b c = refl
assoc′ ω^ aa + ab [ ar ] 𝟎 c = refl
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] c with <-tri aa ba
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] c | inj₁ x = <-⊔ₒ-right _ _ (a<b→a<b⊔c _ _ c (<₂ x)) ⁻¹
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] 𝟎 | inj₂ (inj₁ x) = <-⊔ₒ-left _ _ (<₂ x) ⁻¹
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] ω^ ca + cb [ cr ] | inj₂ (inj₁ x) with <-tri ba ca
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] ω^ ca + cb [ cr ] | inj₂ (inj₁ x) | inj₁ x₁ = refl
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] ω^ ca + cb [ cr ] | inj₂ (inj₁ x) | inj₂ (inj₁ y) 
  rewrite <-⊔ₒ-left _ _ (<₂ {b = bb} {r = br} {d = ab} {s = ar} x) | <-⊔ₒ-left _ _ (<₂ {b = cb} {r = cr} {d = ab} {s = ar} (<-trans y x)) = refl
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] ω^ ca + cb [ cr ] | inj₂ (inj₁ x) | inj₂ (inj₂ refl) with <-tri bb cb 
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] _ | inj₂ (inj₁ x) | _ | inj₁ x₁ = refl
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] _ | inj₂ (inj₁ x) | _ | inj₂ (inj₁ x₁) with <-tri aa ba
assoc′ _ _ _ | inj₂ (inj₁ x) | _ | inj₂ (inj₁ x₁) | inj₁ y = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
assoc′ _ _ _ | inj₂ (inj₁ x) | _ | inj₂ (inj₁ x₁) | inj₂ (inj₁ x₂) = refl
assoc′ _ _ _ | inj₂ (inj₁ x) | _ | inj₂ (inj₁ x₁) | inj₂ (inj₂ refl) = ⊥-elim (<-irrefl x)
assoc′ _ _ _ | inj₂ (inj₁ x) | _ | inj₂ (inj₂ refl) = refl
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] c | inj₂ (inj₂ refl) with <-tri ab bb
assoc′ _ _ c | inj₂ (inj₂ refl) | inj₁ x = <-⊔ₒ-right _ _ (a<b→a<b⊔c _ _ c (<₃ refl x)) ⁻¹
assoc′ _ _ 𝟎 | inj₂ (inj₂ refl) | inj₂ (inj₁ x) = <-⊔ₒ-left _ _ (<₃ refl x) ⁻¹
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] ω^ ca + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) with <-tri aa ca 
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ ca + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₁ y 
  rewrite <-⊔ₒ-right _ _ (<₂ {b = ab} {r = ar} {d = cb} {s = cr} y) = refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ ca + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₁ x₁) 
  rewrite <-⊔ₒ-left _ _ (<₃ {a = aa} {r = br} {s = ar} refl x) = refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ ca + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₂ refl) with <-tri ab cb | <-tri bb cb 
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ aa + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₁ y | inj₁ x₂ 
  rewrite <-⊔ₒ-right _ _ (<₃ {a = aa} {r = ar} {s = cr} refl y) = refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ aa + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₁ x₁ | inj₂ (inj₁ x₂) 
   = ⊥-elim (Lm[≥→¬<] (inj₁ x) (<-trans x₁ x₂))
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ aa + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₁ y | inj₂ (inj₂ refl) = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ aa + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₂ (inj₁ y) | inj₁ x₁ 
  rewrite <-⊔ₒ-left _ _ (<₃ {a = aa} {r = cr} {s = ar} refl y) = refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ aa + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) | inj₁ x₁ 
  rewrite idem′⁼-right aa ab ar cr = refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ aa + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₂ (inj₁ x₁) | inj₂ (inj₁ x₂) 
  rewrite <-⊔ₒ-left _ _ (<₃ {a = aa} {r = br} {s = ar} refl x) = refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ aa + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₂ (inj₁ x₁) | inj₂ (inj₂ refl) 
  rewrite <-⊔ₒ-left _ _ (<₃ {a = aa} {r = cr} {s = ar} refl x) = refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ aa + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) | inj₂ (inj₁ x₁) 
  rewrite <-⊔ₒ-left _ _ (<₃ {a = aa} {r = br} {s = ar} refl x)  = MutualOrd⁼ refl refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ aa + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) 
  rewrite idem′⁼-right aa ab ar cr = refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] 𝟎 | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) rewrite idem′⁼-right aa ab ar br = refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] ω^ ca + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) with <-tri aa ca
assoc′ _ _ _ | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) | inj₁ x = <-⊔ₒ-right _ _ (<₂ x) ⁻¹
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] _ | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) | inj₂ (inj₁ x) rewrite idem′⁼-right aa ab ar br = refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + ab [ br ] ω^ ca + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) with <-tri ab cb 
assoc′ _ _ _ | _ | _ | _ | inj₁ x = <-⊔ₒ-right _ _ (<₃ refl x) ⁻¹
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] _ | _ | _ | _ | inj₂ (inj₁ x) rewrite idem′⁼-right aa bb ar br = refl
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] ω^ ca + cb [ cr ] | _ | _ | _ | inj₂ (inj₂ refl) rewrite idem′⁼-right aa ab ar cr = refl

¬ω^a+b<b : ∀ {a b : MutualOrd} {r : a ≥ fst b} → ¬ (ω^ a + b [ r ] < b)
¬ω^a+b<b {r = r} (<₂ a<c) = ⊥-elim (Lm[≥→¬<] r a<c)
¬ω^a+b<b (<₃ refl x)      = ⊥-elim (¬ω^a+b<b x)

¬ω^a+ω^a+b<b : ∀ {a b : MutualOrd} {r s} → ¬ (ω^ a + ω^ a + b [ r ] [ s ] < b)
¬ω^a+ω^a+b<b {r = r} (<₂ a<c) = ⊥-elim (Lm[≥→¬<] r a<c)
¬ω^a+ω^a+b<b (<₃ {s = s} refl (<₂ a<c)) = ⊥-elim (Lm[≥→¬<] s a<c)
¬ω^a+ω^a+b<b (<₃ refl (<₃ refl x)) = ⊥-elim (¬ω^a+ω^a+b<b x)

infl′ : ∀ (a b c : MutualOrd) r s t u → 
  ω^ a + ω^ b + c [ r ] [ s ] ⊔ₒ c ≡ ω^ a + (ω^ b + c [ t ] ⊔ₒ c) [ u ]
infl′ a b 𝟎 r s t u = MutualOrd⁼ refl (MutualOrd⁼ refl refl)
infl′ a b ω^ ca + cb [ cr ] r s t u with <-tri a ca | <-tri b ca
infl′ a b ω^ ca + cb [ cr ] r s t u | inj₁ x | inj₁ y = ⊥-elim (Lm[≥→¬<] u x)
infl′ a b ω^ ca + cb [ cr ] r s t u | inj₁ x | inj₂ (inj₁ y) = ⊥-elim (Lm[≥→¬<] (inj₁ (<≤-trans y u)) x)
infl′ a b ω^ ca + cb [ cr ] r s t u | inj₁ x | inj₂ (inj₂ refl) with <-tri ω^ b + cb [ cr ] cb 
infl′ a b ω^ b + cb [ cr ] r s t u | inj₁ x | inj₂ (inj₂ refl) | inj₁ x₁ = ⊥-elim (Lm[≥→¬<] u x)
infl′ a b ω^ b + cb [ cr ] r s t u | inj₁ x | inj₂ (inj₂ refl) | inj₂ (inj₁ x₁) = ⊥-elim (Lm[≥→¬<] u x)
infl′ a b ω^ ca + cb [ cr ] r s t u | inj₂ (inj₁ x) | inj₁ y = ⊥-elim (Lm[≥→¬<] r y)
infl′ a b ω^ ca + cb [ cr ] r s t u | inj₂ (inj₂ refl) | inj₁ x₁ with <-tri ω^ b + ω^ a + cb [ cr ] [ r ] cb 
infl′ a b ω^ a + cb [ cr ] r s t u | inj₂ (inj₂ refl) | inj₁ x | inj₁ y = ⊥-elim (Lm[≥→¬<] t x)
infl′ a b ω^ a + cb [ cr ] r s t u | inj₂ (inj₂ refl) | inj₁ x | inj₂ (inj₁ x₁) = ⊥-elim (Lm[≥→¬<] t x)
infl′ a b ω^ ca + cb [ cr ] r s t u | inj₂ (inj₁ x) | inj₂ (inj₁ y) = MutualOrd⁼ refl (MutualOrd⁼ refl (MutualOrd⁼ refl refl))
infl′ a b ω^ ca + cb [ cr ] r s t u | inj₂ (inj₂ refl) | inj₂ (inj₁ x) with <-tri ω^ b + ω^ ca + cb [ cr ] [ r ] cb
infl′ a b ω^ a + cb [ cr ] r s t u | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₁ x₁ = ⊥-elim (Lm[≥→¬<] u x)
infl′ a b ω^ a + cb [ cr ] r s t u | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₁ x₁) = ⊥-elim (Lm[≥→¬<] u x)
infl′ a b ω^ ca + cb [ cr ] r s t u | inj₂ (inj₁ x) | inj₂ (inj₂ refl) with  <-tri ω^ b + cb [ cr ] cb 
infl′ a b ω^ b + cb [ cr ] r s t u | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₁ y = ⊥-elim (¬ω^a+b<b y)
infl′ a b ω^ b + cb [ cr ] r s t u | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₂ (inj₁ x₁) = MutualOrd⁼ refl (MutualOrd⁼ refl (MutualOrd⁼ refl refl))
infl′ a b ω^ ca + cb [ cr ] r s t u | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) with <-tri ω^ a + ω^ a + cb [ cr ] [ r ] cb | <-tri ω^ a + cb [ cr ] cb
infl′ a a ω^ a + cb [ cr ] r s t u | _ | _ | inj₁ x | inj₁ y = ⊥-elim (¬ω^a+b<b y)
infl′ a a ω^ a + cb [ cr ] r s t u | _ | _ | inj₁ x | inj₂ (inj₁ y) = ⊥-elim (¬ω^a+ω^a+b<b x)
infl′ a a ω^ a + cb [ cr ] r s t u | _ | _ | inj₂ (inj₁ x) | inj₁ y = ⊥-elim (¬ω^a+b<b y)
infl′ a a ω^ a + cb [ cr ] r s t u | _ | _ | inj₂ (inj₁ x) | inj₂ (inj₁ x₁) = MutualOrd⁼ refl (MutualOrd⁼ refl (MutualOrd⁼ refl refl))

comm′ : ∀ (a b : MutualOrd) → 
  (a ⊔ₒ b) ≡ (b ⊔ₒ a)
comm′ 𝟎 𝟎 = refl
comm′ 𝟎 ω^ b + b₁ [ x ] = refl
comm′ ω^ a + a₁ [ x ] 𝟎 = refl
comm′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] with <-tri aa ba | <-tri ba aa
comm′ _ _ | inj₁ x | inj₁ y = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
comm′ _ _ | inj₁ x | inj₂ (inj₁ x₁) = refl
comm′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] | inj₁ x | inj₂ (inj₂ refl) with <-tri bb ab 
comm′ _ _  | inj₁ x | inj₂ (inj₂ refl) | inj₁ x₁ = ⊥-elim (<-irrefl x)
comm′ _ _  | inj₁ x | inj₂ (inj₂ refl) | inj₂ (inj₁ x₁) = refl
comm′ _ _  | inj₁ x | inj₂ (inj₂ refl) | inj₂ (inj₂ y) = ⊥-elim (<-irrefl x)
comm′ _ _  | inj₂ (inj₁ x₁) | inj₁ x = refl
comm′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] | inj₂ (inj₂ refl) | inj₁ x with <-tri ab bb 
comm′ _ _ | inj₂ (inj₂ refl) | inj₁ x | inj₁ x₁ = ⊥-elim (<-irrefl x)
comm′ _ _ | inj₂ (inj₂ refl) | inj₁ x | inj₂ (inj₁ x₁) = ⊥-elim (<-irrefl x)
comm′ _ _ | inj₂ (inj₂ refl) | inj₁ x | inj₂ (inj₂ refl) = MutualOrd⁼ refl refl
comm′ _ _ | inj₂ (inj₁ x) | inj₂ (inj₁ y) = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
comm′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] | inj₂ (inj₁ x) | inj₂ (inj₂ refl) with <-tri bb ab 
comm′ _ _ | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₁ x₁ = ⊥-elim (<-irrefl x)
comm′ _ _ | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₂ (inj₁ x₁) = ⊥-elim (<-irrefl x)
comm′ _ _ | inj₂ (inj₁ x) | inj₂ (inj₂ refl) | inj₂ (inj₂ y) = refl
comm′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] | inj₂ (inj₂ refl) | inj₂ (inj₁ x) with <-tri ab bb
comm′ _ _ | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₁ x₁ = refl
comm′ _ _ | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₁ x₁) = ⊥-elim (<-irrefl x)
comm′ _ _ | inj₂ (inj₂ refl) | inj₂ (inj₁ x) | inj₂ (inj₂ refl) = refl
comm′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) with <-tri ab bb | <-tri bb ab
comm′ _ _ | _ | _ | inj₁ x | inj₁ y = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
comm′ _ _ | _ | _ | inj₁ x | inj₂ (inj₁ x₁) = refl
comm′ _ _ | _ | _ | inj₁ x | inj₂ (inj₂ refl) = ⊥-elim (<-irrefl x)
comm′ _ _ | _ | _ | inj₂ (inj₁ x₁) | inj₁ x = refl
comm′ _ _ | _ | _ | inj₂ (inj₂ refl) | inj₁ x = ⊥-elim (<-irrefl x)
comm′ _ _ | _ | _ | inj₂ (inj₁ x) | inj₂ (inj₁ y) = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
comm′ _ _ | _ | _ | inj₂ (inj₁ x) | inj₂ (inj₂ y) = refl
comm′ _ _ | _ | _ | inj₂ (inj₂ refl) | inj₂ (inj₁ x) = refl
comm′ _ _ | _ | _ | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) = MutualOrd⁼ refl refl


subsumption-add′ : ∀ (a b : MutualOrd) (s : a ≥ fst b) → 
  b ⊔ₒ ω^ a + b [ s ] ≡ ω^ a + b [ s ]
subsumption-add′ a 𝟎              s = refl 
subsumption-add′ a ω^ b + d [ r ] s with <-tri b a 
... | inj₁ _          = refl
... | inj₂ (inj₁ a<b) = ⊥-elim (Lm[≥→¬<] s a<b)
... | inj₂ (inj₂ refl) with <-tri d ω^ b + d [ r ]
... | inj₁ _ = refl
... | inj₂ (inj₁ ω^b+d<d) = (⊥-elim (¬ω^a+b<b ω^b+d<d)) 

¬ω^a+b<a : ∀ {a b : MutualOrd} {r : a ≥ fst b} → ¬ (ω^ a + b [ r ] < a)
¬ω^a+b<a (<₂ x) = ⊥-elim (¬ω^a+b<a x)

subsumption-exp′ : ∀ (a b : MutualOrd) (s : a ≥ fst b) → 
  a ⊔ₒ ω^ a + b [ s ] ≡ ω^ a + b [ s ]
subsumption-exp′ 𝟎                b s = refl 
subsumption-exp′ ω^ aa + ab [ r ] b s with <-tri aa (ω^ aa + ab [ r ])
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