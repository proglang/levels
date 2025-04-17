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
  β-suc-zero      : suc zero ≡ ω^ zero + zero         -- definitional
  β-suc-ω         : suc (ω^ ℓ₁ + ℓ₂) ≡ ω^ ℓ₁ + suc ℓ₂ -- definitional
  distributivity  : ω^ ℓ + (ℓ₁ ⊔ ℓ₂) ≡ ω^ ℓ + ℓ₁ ⊔ ω^ ℓ + ℓ₂

data _∊_ : Level → Level → Set where
  id  : ∀ {ℓ : Level} → ℓ ∊ ℓ
  add : ∀ {ℓ ℓ₂ : Level} (ℓ₁ : Level) → ℓ ∊ ℓ₂ → ℓ ∊ ω^ ℓ₁ + ℓ₂ 
  exp : ∀ {ℓ ℓ₁ : Level} (ℓ₂ : Level) → ℓ ∊ ℓ₁ → ℓ ∊ ω^ ℓ₁ + ℓ₂

postulate
  subsumption : ℓ₁ ∊ ℓ₂ → ℓ₁ ⊔ ℓ₂ ≡ ℓ₂

  -- in reality Agda would apply an infinite set of equations:
  --   sub-addₙₘ for all n, m ∈ ℕ
  --   sub-expₙₘ for all n, m ∈ ℕ
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


a≥𝟎 = ≥𝟎

ω^⟨_⟩ : MutualOrd → MutualOrd
--!! MOExAbbr
ω^⟨ a ⟩ = ω^ a + 𝟎 [ a≥𝟎 ]

𝟏 𝟐 ω ω+1 ω² : MutualOrd
--!! MOExA
𝟏 = ω^ 𝟎 + 𝟎 [ a≥𝟎 ]
𝟐 = ω^ 𝟎 + 𝟏 [ inj₂ refl ]
--!! MOExB
ω = ω^ 𝟏 + 𝟎 [ a≥𝟎 ]
ω+1 = ω^ 𝟏 + 𝟏 [ inj₁ <₁ ]
--!! MOExC
ω² = ω^ 𝟐 + 𝟎 [ a≥𝟎 ]
ω²+1 = ω^ 𝟐 + 𝟏 [ inj₁ <₁ ]

-- Successor & Maximum Operation on MutualOrd ---------------------------------

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂) 

--! MOsuc {
sucₒ : MutualOrd → MutualOrd
fst-ignores-suc : ∀ a → (fst a) ≡ fst (sucₒ a)

sucₒ 𝟎 = 𝟏
sucₒ ω^ a + b [ r ] = ω^ a + 
  sucₒ b [ subst (a ≥_) (fst-ignores-suc b) r ]

fst-ignores-suc 𝟎              = refl
fst-ignores-suc ω^ a + b [ r ] = refl
--! }

--! MOlub
_⊔ₒ_ : MutualOrd → MutualOrd → MutualOrd
𝟎 ⊔ₒ              a              = a
a              ⊔ₒ 𝟎              = a
ω^ a + b [ r ] ⊔ₒ ω^ c + d [ s ] with <-tri a c 
... | inj₁ a<c        = ω^ c + d [ s ]
... | inj₂ (inj₁ a>c) = ω^ a + b [ r ]
... | inj₂ (inj₂ a=c) with <-tri b d 
... | inj₁ b<d        = ω^ c + d [ s ]
... | inj₂ (inj₁ b>d) = ω^ a + b [ r ]
... | inj₂ (inj₂ b=d) = ω^ c + d [ s ]

-- Interaction between the Level and MutualOrd Representation -----------------

β-suc-⌊⌋ : ∀ a → suc ⌊ a ⌋ ≡ ⌊ sucₒ a ⌋
β-suc-⌊⌋ 𝟎 = β-suc-zero
β-suc-⌊⌋ (ω^ a + b [ r ]) =  subst (λ x → suc (ω^ ⌊ a ⌋ + ⌊ b ⌋) ≡ ω^ ⌊ a ⌋ + x)
  (β-suc-⌊⌋ b) (β-suc-ω {⌊ a ⌋} {⌊ b ⌋}) 

postulate
   ⊔-^-a<c : {a c : MutualOrd} → a < c → ω^ ⌊ a ⌋ + ℓ₁ ⊔ ω^ ⌊ c ⌋ + ℓ₂ ≡ ω^ ⌊ c ⌋ + ℓ₂
   ⊔-a<c : {a c : MutualOrd} → a < c → ⌊ a ⌋ ⊔ ⌊ c ⌋ ≡ ⌊ c ⌋

β-⊔-⌊⌋ : ∀ a b → ⌊ a ⌋ ⊔ ⌊ b ⌋ ≡ ⌊ a ⊔ₒ b ⌋
β-⊔-⌊⌋ 𝟎 b = refl
β-⊔-⌊⌋ ω^ a + a₁ [ r ] 𝟎 = refl
β-⊔-⌊⌋ ω^ a + b [ r ] ω^ c + d [ s ] with <-tri a c
... | inj₁ a<c = ⊔-^-a<c {ℓ₁ = ⌊ b ⌋}{ℓ₂ = ⌊ d ⌋} a<c
... | inj₂ (inj₁ a>c) = ⊔-^-a<c {ℓ₁ = ⌊ d ⌋}{ℓ₂ = ⌊ b ⌋} a>c
... | inj₂ (inj₂ refl) with <-tri b d
... | inj₁ b<d = trans (sym (distributivity {ℓ = ⌊ a ⌋} {ℓ₁ = ⌊ b ⌋} {ℓ₂ = ⌊ d ⌋})) (cong (ω^ ⌊ a ⌋ +_) (⊔-a<c b<d))
... | inj₂ (inj₁ b>d) = trans (sym (distributivity {ℓ = ⌊ a ⌋} {ℓ₁ = ⌊ b ⌋} {ℓ₂ = ⌊ d ⌋}))
                          ((cong (ω^ ⌊ a ⌋ +_) (⊔-a<c b>d)))
... | inj₂ (inj₂ refl) = refl

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
MutualOrd→ℕ a (<₂ {b = b} {inj₂ y} <₁) = ℕ.suc (MutualOrd→ℕ b (fst[a]≡0→a<ω b (sym y)))

fst[ℕ→MutualOrd]≡0 : ∀ n → fst (ℕ→MutualOrd n) ≡ 𝟎
fst[ℕ→MutualOrd]≡0 ℕ.zero    = refl
fst[ℕ→MutualOrd]≡0 (ℕ.suc n) = 
    trans (sym (fst-ignores-suc (ℕ→MutualOrd n))) (fst[ℕ→MutualOrd]≡0 n)

ω+ₙ_ : ℕ → MutualOrd
ω+ₙ n = ω^ 𝟏 + ℕ→MutualOrd n [ subst (𝟏 ≥_) (sym (fst[ℕ→MutualOrd]≡0 n)) (inj₁ <₁) ]

-- Properties for Successor and Maximum Operation ------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)

distributivity′ : ∀ (a b c : MutualOrd) 
                  (r : a ≥ fst (b ⊔ₒ c)) (s : a ≥ fst b) (t : a ≥ fst c) →
--!! Dist
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

right-id′  : ∀ a → 
--!! Neut
  (a ⊔ₒ 𝟎) ≡ a

right-id′  𝟎 = refl
right-id′  ω^ a + a₁ [ x ] = refl

idem′ : ∀ a → 
--!! Idem
  (a ⊔ₒ a) ≡ a

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
a<b→a<b⊔c a b 𝟎 a<b = subst (_ <_) (sym (right-id′ _)) a<b
a<b→a<b⊔c a ω^ ba + bb [ br ] ω^ ca + cb [ cr ] a<b with <-tri ba ca
... | inj₁ x = <-trans a<b (<₂ x)
... | inj₂ (inj₁ x) = a<b
... | inj₂ (inj₂ refl) with <-tri bb cb 
... | inj₁ x = <-trans a<b (<₃ refl x)
... | inj₂ (inj₁ x) = a<b
... | inj₂ (inj₂ refl) = subst (a <_) (MutualOrd⁼ refl refl) a<b

assoc′ : ∀ (a b c : MutualOrd) →
--!! Assoc 
  (a ⊔ₒ b) ⊔ₒ c ≡ a ⊔ₒ (b ⊔ₒ c)

assoc′ 𝟎 b c = refl
assoc′ ω^ aa + ab [ ar ] 𝟎 c = refl
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] c with <-tri aa ba
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] c | inj₁ x = sym (<-⊔ₒ-right _ _ (a<b→a<b⊔c _ _ c (<₂ x)))
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] 𝟎 | inj₂ (inj₁ x) = sym (<-⊔ₒ-left _ _ (<₂ x))
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
assoc′ _ _ c | inj₂ (inj₂ refl) | inj₁ x = sym (<-⊔ₒ-right _ _ (a<b→a<b⊔c _ _ c (<₃ refl x)))
assoc′ _ _ 𝟎 | inj₂ (inj₂ refl) | inj₂ (inj₁ x) = sym (<-⊔ₒ-left _ _ (<₃ refl x))
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
assoc′ _ _ _ | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) | inj₁ x = sym (<-⊔ₒ-right _ _ (<₂ x))
assoc′ ω^ aa + ab [ ar ] ω^ aa + bb [ br ] _ | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) | inj₂ (inj₁ x) rewrite idem′⁼-right aa ab ar br = refl
assoc′ ω^ aa + ab [ ar ] ω^ aa + ab [ br ] ω^ ca + cb [ cr ] | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) with <-tri ab cb 
assoc′ _ _ _ | _ | _ | _ | inj₁ x = sym (<-⊔ₒ-right _ _ (<₃ refl x))
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] _ | _ | _ | _ | inj₂ (inj₁ x) rewrite idem′⁼-right aa bb ar br = refl
assoc′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] ω^ ca + cb [ cr ] | _ | _ | _ | inj₂ (inj₂ refl) rewrite idem′⁼-right aa ab ar cr = refl

¬ω^a+b<b : ∀ {a b : MutualOrd} {r : a ≥ fst b} → ¬ (ω^ a + b [ r ] < b)
¬ω^a+b<b {r = r} (<₂ a<c) = ⊥-elim (Lm[≥→¬<] r a<c)
¬ω^a+b<b (<₃ refl x)      = ⊥-elim (¬ω^a+b<b x)

¬ω^a+ω^a+b<b : ∀ {a b : MutualOrd} {r s} → ¬ (ω^ a + ω^ a + b [ r ] [ s ] < b)
¬ω^a+ω^a+b<b {r = r} (<₂ a<c) = ⊥-elim (Lm[≥→¬<] r a<c)
¬ω^a+ω^a+b<b (<₃ {s = s} refl (<₂ a<c)) = ⊥-elim (Lm[≥→¬<] s a<c)
¬ω^a+ω^a+b<b (<₃ refl (<₃ refl x)) = ⊥-elim (¬ω^a+ω^a+b<b x)

⊔ₒ-fst : ∀ a b c r → (ω^ a + b [ r ] ⊔ₒ c) ≡ c → a ≤ fst c
⊔ₒ-fst a b ω^ ca + cb [ cr ] r eq with <-tri a ca 
... | inj₁ x = inj₁ x
⊔ₒ-fst a b ω^ ca + cb [ cr ] r refl | inj₂ (inj₁ x) = ⊥-elim (<-irrefl x)
... | inj₂ (inj₂ refl) with <-tri b cb
⊔ₒ-fst a b ω^ a + cb [ cr ] r refl | inj₂ (inj₂ refl) | inj₁ x = inj₂ refl
⊔ₒ-fst a b ω^ a + cb [ cr ] r refl | inj₂ (inj₂ refl) | inj₂ (inj₁ x) = ⊥-elim (<-irrefl x)
⊔ₒ-fst a b ω^ a + cb [ cr ] r refl | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) = inj₂ refl

≤<-trans : ∀ {a b c} → a ≤ b → b < c → a < c
≤<-trans (inj₁ a<b) b<c = <-trans a<b b<c
≤<-trans (inj₂ refl) b<c = b<c 

⊔ₒ-rest : ∀ a b c r → (ω^ a + b [ r ] ⊔ₒ c) ≡ c → b ≤ c
⊔ₒ-rest a b ω^ ca + cb [ cr ] r eq with <-tri a ca
⊔ₒ-rest a 𝟎 ω^ ca + cb [ cr ] r refl | inj₁ x = inj₁ <₁
⊔ₒ-rest a ω^ ba + bb [ br ] ω^ ca + cb [ cr ] r refl | inj₁ x = inj₁ (<₂ (≤<-trans r x))
⊔ₒ-rest a b ω^ ca + cb [ cr ] r refl | inj₂ (inj₁ x) = ⊥-elim (<-irrefl x)
⊔ₒ-rest a b ω^ ca + cb [ cr ] r eq | inj₂ (inj₂ refl) with <-tri b cb 
⊔ₒ-rest a 𝟎 ω^ a + cb [ cr ] r refl | inj₂ (inj₂ refl) | inj₁ x = inj₁ <₁
⊔ₒ-rest a ω^ ba + bb [ br ] ω^ a + cb [ cr ] r refl | inj₂ (inj₂ refl) | inj₁ x = inj₁ (<-trans x (rest< _ _ _))
⊔ₒ-rest a b ω^ a + cb [ cr ] r refl | inj₂ (inj₂ refl) | inj₂ (inj₁ x) = ⊥-elim (<-irrefl x)
⊔ₒ-rest a 𝟎 ω^ a + cb [ cr ] r refl | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) = inj₁ <₁
⊔ₒ-rest a ω^ ba + bb [ br ] ω^ a + ω^ ba + bb [ br ] [ cr ] r refl | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) = inj₁ (rest< _ _ _)

fst[a]≤a : ∀ a → fst a ≤ a
fst[a]≤a 𝟎 = inj₂ refl
fst[a]≤a ω^ a + a₁ [ r ] = inj₁ (fst< _ _ _)

a≡fst[a]→a≡𝟎 : ∀ a → fst a ≡ a → a ≡ 𝟎
a≡fst[a]→a≡𝟎 𝟎 refl = refl

data _∊′_ : MutualOrd → MutualOrd → Set where
  id  : ∀ a → a ∊′ a
  add : ∀ (a b c : MutualOrd) r → a ∊′ c → a ∊′ ω^ b + c [ r ]
  exp : ∀ (a b c : MutualOrd) r → a ∊′ b → a ∊′ ω^ b + c [ r ]

¬ω^a+b⊔a≡a : ∀ a b r → ¬ (a ≡ (ω^ a + b [ r ] ⊔ₒ a))
¬ω^a+b⊔a≡a 𝟎 b r = 𝟎≢ω
¬ω^a+b⊔a≡a ω^ aa + ab [ ar ] b r with <-tri ω^ aa + ab [ ar ] aa 
... | inj₁ x = ⊥-elim (Lm[≥→¬<] (inj₁ (fst< _ _ _)) x)
... | inj₂ (inj₁ x) = λ { () }

subsumption′ : ∀ (a b : MutualOrd) → 
--!! Subsum
  a ∊′ b → a ⊔ₒ b ≡ b

subsumption′ a b (id .a) = idem′ a
subsumption′ 𝟎 b (add .𝟎 b₁ c r x) = refl
subsumption′ ω^ aa + ab [ ar ] ω^ ba + bb [ br ] (add .(ω^ aa + ab [ ar ]) .ba .bb r x) with <-tri aa ba
... | inj₁ y = refl
... | inj₂ (inj₁ y) = ⊥-elim (Lm[≥→¬<] (≤-trans (⊔ₒ-fst _ _ _ _ (subsumption′ _ _ x)) r) y)
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ y = refl
... | inj₂ (inj₂ refl) = refl
... | inj₂ (inj₁ y) = ⊥-elim (Lm[≥→¬<] (⊔ₒ-rest _ _ _ _ (subsumption′ _ _ x)) y) 
subsumption′ 𝟎 b (exp .𝟎 b₁ c r x) = refl
subsumption′ ω^ aa + ab [ ar ] b (exp .(ω^ aa + ab [ ar ]) b₁ c r x) with <-tri aa b₁
... | inj₁ x₁ = refl
... | inj₂ (inj₁ y) = ⊥-elim (Lm[≥→¬<] (≤-trans (⊔ₒ-fst _ _ _ _ (subsumption′ _ _ x)) (fst[a]≤a _)) y)
... | inj₂ (inj₂ refl) with <-tri ab c 
... | inj₁ y = refl
... | inj₂ (inj₂ refl) = refl
... | inj₂ (inj₁ y) = ⊥-elim (¬ω^a+b⊔a≡a _ _ _ (sym (subsumption′ _ _ x))) 

comm′ : ∀ (a b : MutualOrd) → 
--!! Comm
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

sub-add₁₀′ : ∀ (a b : MutualOrd) (s : a ≥ fst b) → 
  b ⊔ₒ ω^ a + b [ s ] ≡ ω^ a + b [ s ]
sub-add₁₀′ a 𝟎              s = refl 
sub-add₁₀′ a ω^ b + d [ r ] s with <-tri b a 
... | inj₁ _          = refl
... | inj₂ (inj₁ a<b) = ⊥-elim (Lm[≥→¬<] s a<b)
... | inj₂ (inj₂ refl) with <-tri d ω^ b + d [ r ]
... | inj₁ _ = refl
... | inj₂ (inj₁ ω^b+d<d) = (⊥-elim (¬ω^a+b<b ω^b+d<d)) 

¬ω^a+b<a : ∀ {a b : MutualOrd} {r : a ≥ fst b} → ¬ (ω^ a + b [ r ] < a)
¬ω^a+b<a (<₂ x) = ⊥-elim (¬ω^a+b<a x)

sub-exp₁₀′ : ∀ (a b : MutualOrd) (s : a ≥ fst b) → 
  a ⊔ₒ ω^ a + b [ s ] ≡ ω^ a + b [ s ]
sub-exp₁₀′ 𝟎                b s = refl 
sub-exp₁₀′ ω^ aa + ab [ r ] b s with <-tri aa (ω^ aa + ab [ r ])
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
  
