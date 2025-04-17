{-# OPTIONS --warn=noUserWarning #-}
module BoundedQuantification where

open import Level
open import ExtendedHierarchy renaming (_≤_ to _≤ₒ_; _<_ to _<ₒ_; _>_ to _>ₒ_)

--! BQ >

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  Λ Λ′ Λ₁ Λ₂ Λ₃ Λ₄ : Level

-- Ordering on Levels ---------------------------------------------------------

-- axiom

--! LevelLe
data _≤_ : Level → Level → Set where
  ≤-id   : ∀ ℓ            → ℓ ≤ ℓ
  ≤-suc  : ℓ ≤ ℓ₂         → ℓ ≤ suc ℓ₂
  ≤-lub  : ∀ ℓ₁ → ℓ ≤ ℓ₂  → ℓ ≤ (ℓ₁ ⊔ ℓ₂) 
  ≤-add  : ∀ ℓ₁ → ℓ ≤ ℓ₂  → ℓ ≤ ω^ ℓ₁ + ℓ₂ 
  ≤-exp  : ∀ ℓ₂ → ℓ ≤ ℓ₁  → ℓ ≤ ω^ ℓ₁ + ℓ₂ 

-- the important thing is, that the left hand side of the inequalities does not 
-- differ to the ones in the hypotheses, 
-- such that we can recurse in the BoundedLift / bounded-lift / bounded-unlift functions 

--! LevelLt
_<_ : Level → Level → Set
_<_ ℓ₁ ℓ₂ = suc ℓ₁ ≤ ℓ₂ 

--! Lim
data Lim : Level → Set where
  lim  : ∀ {ℓ}  → zero < ℓ  → Lim (ω^ ℓ + zero)
  add  : ∀ ℓ₁   → Lim ℓ₂    → Lim (ω^ ℓ₁ + ℓ₂)
  
postulate 
--! AxiomsLe
  ≤-lublub   : ℓ₁ ≤ ℓ₃ → ℓ₂ ≤ ℓ₃ → (ℓ₁ ⊔ ℓ₂) ≤ ℓ₃
  <-suc-lim  : ∀ ℓ₁ ℓ₂ → ℓ₁ < ℓ₂ → Lim ℓ₂ → suc ℓ₁ < ℓ₂

  -- unification fails
  -- no injectivity of suc / ω^_+_ on postulates!
  -- proven on MutualOrd representation below
  -- propose to add injectivity? does this lead to inconsistency?

-- Bounded Quantification -----------------------------------------------------
--! BoundedLevel
record BoundedLevel (Λ : Level) : Set where
  constructor _,_  
  field  #_ : Level ;  #<Λ : #_ < Λ

open BoundedLevel public

bound : BoundedLevel Λ → Level
bound {Λ} _ = Λ

-- Lifiting using Ordering ----------------------------------------------------

--! BoundedLift
BoundedLift  : ℓ ≤ Λ → Set ℓ → Set Λ
BoundedLift (≤-id ℓ)                  A = Lift ℓ A
BoundedLift (≤-suc {ℓ₂ = ℓ₂} ℓ≤Λ)     A = Lift (suc ℓ₂) (BoundedLift ℓ≤Λ A)
BoundedLift (≤-lub ℓ₂ ℓ≤Λ)            A = Lift ℓ₂ (BoundedLift ℓ≤Λ A)
BoundedLift (≤-add {ℓ₂ = ℓ₂} ℓ₁ ℓ≤Λ)  A = cast (subsumption {ℓ₁ = ℓ₂} (add ℓ₁ id)) (Lift (ω^ ℓ₁ + ℓ₂) (BoundedLift ℓ≤Λ A))
BoundedLift (≤-exp {ℓ₁ = ℓ₁} ℓ₂ ℓ≤Λ)  A = cast (subsumption {ℓ₁ = ℓ₁} (exp ℓ₂ id)) (Lift (ω^ ℓ₁ + ℓ₂) (BoundedLift ℓ≤Λ A))

bounded-lift : ∀ (ℓ≤Λ : ℓ ≤ Λ) → {A : Set ℓ} → A → BoundedLift ℓ≤Λ A
bounded-lift (≤-id ℓ)      a = lift a
bounded-lift (≤-suc ℓ≤Λ)   a = lift (bounded-lift ℓ≤Λ a)
bounded-lift (≤-lub _ ℓ≤Λ) a = lift (bounded-lift ℓ≤Λ a)
bounded-lift (≤-add _ ℓ≤Λ) a = cast-intro _ (lift (bounded-lift ℓ≤Λ a))
bounded-lift (≤-exp _ ℓ≤Λ) a = cast-intro _ (lift (bounded-lift ℓ≤Λ a))

bounded-unlift : ∀ (ℓ≤Λ : ℓ ≤ Λ) → {A : Set ℓ} → BoundedLift ℓ≤Λ A → A
bounded-unlift (≤-id ℓ)      (Level.lift a) = a
bounded-unlift (≤-suc ℓ≤Λ)   (Level.lift a) = bounded-unlift ℓ≤Λ a
bounded-unlift (≤-lub _ ℓ≤Λ) (Level.lift a) = bounded-unlift ℓ≤Λ a
bounded-unlift (≤-add {ℓ₂ = ℓ₂} ℓ₁ ℓ≤Λ) {A = A} a with cast-elim _ {A = Lift (ω^ ℓ₁ + ℓ₂) (BoundedLift ℓ≤Λ A)} a
... | lift a = bounded-unlift ℓ≤Λ a 
bounded-unlift (≤-exp {ℓ₁ = ℓ₁} ℓ₂ ℓ≤Λ) {A = A} a with cast-elim _ {A = Lift (ω^ ℓ₁ + ℓ₂) (BoundedLift ℓ≤Λ A)} a
... | lift a = bounded-unlift ℓ≤Λ a 

-- Properties for Lifiting using Ordering -------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

module Properties where  
  unlift-lift-cancel : ∀ (ℓ≤Λ : ℓ ≤ Λ) {A : Set ℓ} → (a : A) → 
    bounded-unlift ℓ≤Λ (bounded-lift ℓ≤Λ a) ≡ a 
  unlift-lift-cancel (≤-id ℓ)      a = refl  
  unlift-lift-cancel (≤-suc ℓ≤Λ)   a = unlift-lift-cancel ℓ≤Λ a
  unlift-lift-cancel (≤-lub _ ℓ≤Λ) a = unlift-lift-cancel ℓ≤Λ a
  unlift-lift-cancel (≤-add {ℓ₂ = ℓ₂} ℓ₁ ℓ≤Λ) a 
    rewrite cast-elim-intro-cancel (subsumption {ℓ₁ = ℓ₂} (add ℓ₁ id)) (lift {ℓ = ω^ ℓ₁ + ℓ₂} (bounded-lift ℓ≤Λ a))
    = unlift-lift-cancel ℓ≤Λ a 
  unlift-lift-cancel (≤-exp {ℓ₁ = ℓ₁} ℓ₂ ℓ≤Λ) a 
    rewrite cast-elim-intro-cancel (subsumption {ℓ₁ = ℓ₁} (exp ℓ₂ id)) (lift {ℓ = ω^ ℓ₁ + ℓ₂} (bounded-lift ℓ≤Λ a))
    = unlift-lift-cancel ℓ≤Λ a

-- Proving the postulates on the MutualOrd Representation ---------------------

≤-id′ : ∀ a → a ≤ₒ a
≤-id′ a = inj₂ refl

<-suc′ : ∀ a b → a <ₒ b → a <ₒ sucₒ b
<-suc′ a b <₁ = <₁
<-suc′ a b (<₂ a<b) = <₂ a<b
<-suc′ a b (<₃ refl a<b) = <₃ refl (<-suc′ _ _ a<b)

≤-suc′ : ∀ a b → a ≤ₒ b → a ≤ₒ sucₒ b
≤-suc′ a b (inj₁ x) = inj₁ (<-suc′ a b x)
≤-suc′ a b (inj₂ refl) = inj₁ (a<suc[a] _)
  where a<suc[a] : ∀ a → a <ₒ sucₒ a 
        a<suc[a] 𝟎 = <₁
        a<suc[a] ω^ a + a₁ [ x ] = <₃ refl (a<suc[a] _)
        
<-lub′ : ∀ a b c → a <ₒ b → a <ₒ (b ⊔ₒ c)
<-lub′ a b 𝟎 a<b = subst (_ <ₒ_) (sym (right-id′ _)) a<b
<-lub′ a ω^ ba + bb [ br ] ω^ ca + cb [ cr ] a<b with <-tri ba ca
... | inj₁ x = <-trans a<b (<₂ x)
... | inj₂ (inj₁ x) = a<b
... | inj₂ (inj₂ refl) with <-tri bb cb 
... | inj₁ x = <-trans a<b (<₃ refl x)
... | inj₂ (inj₁ x) = a<b
... | inj₂ (inj₂ refl) = subst (a <ₒ_) (MutualOrd⁼ refl refl) a<b 

≤-lub′ :  ∀ a b c → a ≤ₒ b → a ≤ₒ (b ⊔ₒ c)
≤-lub′ a b c (inj₁ x) = inj₁ (<-lub′ _ _ _ x)
≤-lub′ a b 𝟎 (inj₂ refl) = inj₂ (right-id′ a)
≤-lub′ 𝟎 b ω^ c + c₁ [ x ] (inj₂ refl) = inj₁ <₁
≤-lub′ ω^ aa + ab [ ar ] b ω^ ca + cb [ cr ] (inj₂ refl) with <-tri aa ca 
... | inj₁ x = inj₁ (<₂ x)
... | inj₂ (inj₁ x) = inj₂ refl
... | inj₂ (inj₂ refl) with <-tri ab cb
... | inj₁ x = inj₁ (<₃ refl x)
... | inj₂ (inj₁ x) = inj₂ refl
... | inj₂ (inj₂ refl) = inj₂ (MutualOrd⁼ refl refl)

≤-add′  : ∀ a b r → a ≤ₒ b → a ≤ₒ ω^ a + b [ r ]
≤-add′ a b r a≤b = inj₁ (fst< _ _ _) 

≤-exp′  : ∀ a b r → a ≤ₒ b → a ≤ₒ ω^ b + a [ r ]
≤-exp′ a b r a≤b = inj₁ (rest< _ _ _) 

data _≤ₒ′_ : MutualOrd → MutualOrd → Set where
  ≤ₒ′-id   : ∀ a                 → a ≤ₒ′ a
  ≤ₒ′-suc  : ∀ a b     → a ≤ₒ′ b → a ≤ₒ′ sucₒ b
  ≤ₒ′-lub  : ∀ a b c   → a ≤ₒ′ b → a ≤ₒ′ (b ⊔ₒ c) 
  ≤ₒ′-add  : ∀ a b c r → a ≤ₒ′ c → a ≤ₒ′ ω^ b + c [ r ] 
  ≤ₒ′-exp  : ∀ a b c r → a ≤ₒ′ b → a ≤ₒ′ ω^ b + c [ r ]

-- completeness : ∀ a b → a ≤ₒ b → a ≤ₒ′ b  
-- completeness a b (inj₁ <₁) = {!   !}
-- completeness ω^ aa + ab [ ar ] ω^ ba + bb [ br ] (inj₁ (<₂ x)) = lemma _ _ _ _ _ _ (completeness _ _ (inj₁ x))
--   where lemma : ∀ a b c d r s → a ≤ₒ′ c → ω^ a + b [ r ] ≤ₒ′ ω^ c + d [ s ]
--         lemma a _ _ _ _ _ (≤ₒ′-id .a) = {!   !}
--         lemma a _ _ _ _ _ (≤ₒ′-suc .a b x) = {!   !}
--         lemma a _ _ _ _ _ (≤ₒ′-lub .a b c x) = {!   !}
--         lemma a _ _ _ _ _ (≤ₒ′-add .a b c r x) = {!   !}
--         lemma a _ _ _ _ _ (≤ₒ′-exp .a b c r x) = {!   !}
-- completeness a b (inj₁ (<₃ x x₁)) = {!   !}
-- completeness a b (inj₂ refl) = ≤ₒ′-id _

data LimOrd : MutualOrd → Set where 
  lim′ : ∀ a → a >ₒ 𝟎 → LimOrd (ω^⟨ a ⟩)
  add′ : ∀ a b r → LimOrd b → LimOrd ω^ a + b [ r ]

LimOrd[a]→fst[a]>𝟎 : ∀ a → LimOrd a → fst a >ₒ 𝟎
LimOrd[a]→fst[a]>𝟎 _ (lim′ _ x)                  = x
LimOrd[a]→fst[a]>𝟎 _ (add′ _ _ (inj₁ x) lima)    = <-trans (LimOrd[a]→fst[a]>𝟎 _ lima) x
LimOrd[a]→fst[a]>𝟎 _ (add′ _ _ (inj₂ refl) lima) = LimOrd[a]→fst[a]>𝟎 _ lima

<-suc-lim′ : ∀ a b → a <ₒ b → LimOrd b → sucₒ a <ₒ b
<-suc-lim′ a b <₁ limb = <₂ (LimOrd[a]→fst[a]>𝟎 _ limb)
<-suc-lim′ a b (<₂ a<b) limb = <₂ a<b
<-suc-lim′ a b (<₃ refl a<b) (add′ _ _ _ limb) = <₃ refl (<-suc-lim′ _ _ a<b limb) 

<-lublub′ : ∀ a b c → a <ₒ c → b <ₒ c → (a ⊔ₒ b) <ₒ c
<-lublub′ a b c <₁ b<c = b<c
<-lublub′ a b c a<c <₁ = subst (_<ₒ _) (sym (right-id′  _)) a<c
<-lublub′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] ω^ ca + cb [ t ] (<₂ a<c) (<₂ b<c) with <-tri aa ba
... | inj₁ x = <₂ b<c
... | inj₂ (inj₁ x) = <₂ a<c
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = <₂ b<c
... | inj₂ (inj₁ x) = <₂ a<c
... | inj₂ (inj₂ refl) = <₂ b<c
<-lublub′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] ω^ ca + cb [ t ] (<₂ a<c) (<₃ refl b<c) with  <-tri aa ba
... | inj₁ x = <₃ refl b<c
... | inj₂ (inj₁ x) = <₂ a<c
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = <₃ refl b<c
... | inj₂ (inj₁ x) = ⊥-elim (<-irrefl a<c)
... | inj₂ (inj₂ refl) = <₃ refl b<c
<-lublub′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] ω^ ca + cb [ t ] (<₃ refl a<c) (<₂ b<c) with <-tri aa ba
... | inj₁ x = <₂ b<c
... | inj₂ (inj₁ x) = <₃ refl a<c
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = ⊥-elim (<-irrefl b<c)
... | inj₂ (inj₁ x) = <₃ refl a<c
... | inj₂ (inj₂ refl) = ⊥-elim (<-irrefl b<c)
<-lublub′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] ω^ ca + cb [ t ] (<₃ refl a<c) (<₃ refl b<c) with <-tri aa aa
... | inj₁ x = <₃ refl b<c
... | inj₂ (inj₁ x) = <₃ refl a<c
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = <₃ refl b<c
... | inj₂ (inj₁ x) = <₃ refl a<c
... | inj₂ (inj₂ refl) = <₃ refl b<c

≤-lublub′ : ∀ a b c → a ≤ₒ c → b ≤ₒ c → (a ⊔ₒ b) ≤ₒ c
≤-lublub′ a b c (inj₁ x) (inj₁ y) = inj₁ (<-lublub′ _ _ _ x y) 
≤-lublub′ a b c (inj₁ x) (inj₂ refl) = inj₂ (sym (<-⊔ₒ-right _ _ x)) 
≤-lublub′ a b c (inj₂ refl) (inj₁ x) = inj₂ (sym (<-⊔ₒ-left _ _ x))       
≤-lublub′ a b c (inj₂ refl) (inj₂ refl) rewrite idem′ a = inj₂ refl 
 