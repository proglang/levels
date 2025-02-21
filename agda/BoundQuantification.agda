{-# OPTIONS --allow-unsolved-metas #-}
module BoundQuantification where

open import Level
open import ExtendedHierarchy renaming (_≤_ to _≤ᵒ_; _<_ to _<ᵒ_; _>_ to _>ᵒ_)

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  Λ Λ′ Λ₁ Λ₂ Λ₃ Λ₄ : Level

-- Ordering on Levels ---------------------------------------------------------

-- axiom

data _≤_ : Level → Level → Set where
  ≤-id  : ∀ ℓ → ℓ ≤ ℓ
  ≤-suc : ℓ₁ ≤ ℓ₂ → ℓ₁ ≤ suc ℓ₂
  ≤-lub : ∀ ℓ₂ → ℓ ≤ ℓ₁ → ℓ ≤ (ℓ₁ ⊔ ℓ₂) 
  ≤-add : ∀ ℓ₁ → ℓ ≤ ℓ₂ → ℓ ≤ ω^ ℓ₁ + ℓ₂ 
  ≤-exp : ∀ ℓ₂ → ℓ ≤ ℓ₁ → ℓ ≤ ω^ ℓ₁ + ℓ₂ 

_<_ : Level → Level → Set
_<_ ℓ₁ ℓ₂ = suc ℓ₁ ≤ ℓ₂ 

-- the important thing is, that the left hand side of the inequalities does not 
-- differ to the ones in the hypotheses, 
-- such that we can recurse in the BoundLift / bound-lift / bound-unlift functions 

data Lim : Level → Set where
  lim : ∀ ℓ → zero < ℓ → Lim (ω^ ℓ + zero)
  add : ∀ ℓ₁ ℓ₂ → Lim ℓ₂ → Lim (ω^ ℓ₁ + ℓ₂)
  
postulate 
  ≤-lublub  : ℓ₁ ≤ ℓ₃ → ℓ₂ ≤ ℓ₃ → (ℓ₁ ⊔ ℓ₂) ≤ ℓ₃
  <-suc-lim : ∀ ℓ₁ ℓ₂ → ℓ₁ < ℓ₂ → Lim ℓ₂ → suc ℓ₁ < ℓ₂
  -- unification fails
  -- no injectivity of suc / ω^_+_ on postulates!
  -- proven on MutualOrd representation below

-- Bounded Quantification -----------------------------------------------------
record BoundLevel (Λ : Level) : Set where
  constructor _,_  
  field 
    # : Level
    #<Λ : # < Λ

open BoundLevel public

bound : BoundLevel Λ → Level
bound {Λ} _ = Λ

-- Lifiting using Ordering ----------------------------------------------------

BoundLift  : ℓ ≤ Λ → Set ℓ → Set Λ
BoundLift (≤-id ℓ)                 A = Lift ℓ A
BoundLift (≤-suc {ℓ₂ = ℓ₂} ℓ≤Λ)    A = Lift (suc ℓ₂) (BoundLift ℓ≤Λ A)
BoundLift (≤-lub ℓ₂ ℓ≤Λ)           A = Lift ℓ₂ (BoundLift ℓ≤Λ A)
BoundLift (≤-add {ℓ₂ = ℓ₂} ℓ₁ ℓ≤Λ) A = cast (subsumption-add₁₀ {ℓ = ℓ₂} {ℓ₁ = ℓ₁}) (Lift (ω^ ℓ₁ + ℓ₂) (BoundLift ℓ≤Λ A))
BoundLift (≤-exp {ℓ₁ = ℓ₁} ℓ₂ ℓ≤Λ) A = cast (subsumption-exp₁₀ {ℓ = ℓ₁} {ℓ₁ = ℓ₂}) (Lift (ω^ ℓ₁ + ℓ₂) (BoundLift ℓ≤Λ A))

bound-lift : ∀ (ℓ≤Λ : ℓ ≤ Λ) → {A : Set ℓ} → A → BoundLift ℓ≤Λ A
bound-lift (≤-id ℓ)      a = lift a
bound-lift (≤-suc ℓ≤Λ)   a = lift (bound-lift ℓ≤Λ a)
bound-lift (≤-lub _ ℓ≤Λ) a = lift (bound-lift ℓ≤Λ a)
bound-lift (≤-add _ ℓ≤Λ) a = cast-push _ (lift (bound-lift ℓ≤Λ a))
bound-lift (≤-exp _ ℓ≤Λ) a = cast-push _ (lift (bound-lift ℓ≤Λ a))

bound-unlift : ∀ (ℓ≤Λ : ℓ ≤ Λ) → {A : Set ℓ} → BoundLift ℓ≤Λ A → A
bound-unlift (≤-id ℓ)      (Level.lift a) = a
bound-unlift (≤-suc ℓ≤Λ)   (Level.lift a) = bound-unlift ℓ≤Λ a
bound-unlift (≤-lub _ ℓ≤Λ) (Level.lift a) = bound-unlift ℓ≤Λ a
bound-unlift (≤-add {ℓ₂ = ℓ₂} ℓ₁ ℓ≤Λ) {A = A} a with cast-pop _ {A = Lift (ω^ ℓ₁ + ℓ₂) (BoundLift ℓ≤Λ A)} a
... | lift a = bound-unlift ℓ≤Λ a 
bound-unlift (≤-exp {ℓ₁ = ℓ₁} ℓ₂ ℓ≤Λ) {A = A} a with cast-pop _ {A = Lift (ω^ ℓ₁ + ℓ₂) (BoundLift ℓ≤Λ A)} a
... | lift a = bound-unlift ℓ≤Λ a 

-- Properties for Lifiting using Ordering -------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans; subst)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

module Properties where  
  unlift-lift-cancel : ∀ (ℓ≤Λ : ℓ ≤ Λ) {A : Set ℓ} → (a : A) → 
    bound-unlift ℓ≤Λ (bound-lift ℓ≤Λ a) ≡ a 
  unlift-lift-cancel (≤-id ℓ)      a = refl  
  unlift-lift-cancel (≤-suc ℓ≤Λ)   a = unlift-lift-cancel ℓ≤Λ a
  unlift-lift-cancel (≤-lub _ ℓ≤Λ) a = unlift-lift-cancel ℓ≤Λ a
  unlift-lift-cancel (≤-add {ℓ₂ = ℓ₂} ℓ₁ ℓ≤Λ) a 
    rewrite cast-pop-push-cancel (subsumption-add₁₀ {ℓ = ℓ₂} {ℓ₁ = ℓ₁}) (lift {ℓ = ω^ ℓ₁ + ℓ₂} (bound-lift ℓ≤Λ a))
    = unlift-lift-cancel ℓ≤Λ a 
  unlift-lift-cancel (≤-exp {ℓ₁ = ℓ₁} ℓ₂ ℓ≤Λ) a -- unlift-lift-cancel ℓ≤Λ a
    rewrite cast-pop-push-cancel (subsumption-exp₁₀ {ℓ = ℓ₁} {ℓ₁ = ℓ₂}) (lift {ℓ = ω^ ℓ₁ + ℓ₂} (bound-lift ℓ≤Λ a))
    = unlift-lift-cancel ℓ≤Λ a

  -- lift-unlift-cancel : ∀ (ℓ≤Λ : ℓ ≤ Λ) {A : Set ℓ} → (a : BoundLift ℓ≤Λ A) → 
  --   bound-lift ℓ≤Λ (bound-unlift ℓ≤Λ a) ≡ a 
  -- lift-unlift-cancel (≤-id ℓ)      a        = refl             
  -- lift-unlift-cancel (≤-suc ℓ≤Λ)   (lift a) = cong lift (lift-unlift-cancel ℓ≤Λ a)
  -- lift-unlift-cancel (≤-lub _ ℓ≤Λ) (lift a) = cong lift (lift-unlift-cancel ℓ≤Λ a)
  -- lift-unlift-cancel (≤-add {ℓ₂ = ℓ₂} ℓ₁ ℓ≤Λ) {A} a with lift-unlift-cancel ℓ≤Λ (lower (cast-pop _ {A = Lift (ω^ ℓ₁ + ℓ₂) (BoundLift ℓ≤Λ A)} a))
  -- ... | ih = {! cong lift ih    !}
  -- lift-unlift-cancel (≤-exp _ ℓ≤Λ) a  =  {!   !}

-- Proving the postulates on the MutualOrd Representation ---------------------

data LimOrd : MutualOrd → Set where 
  lim′ : ∀ a → a >ᵒ 𝟎 → LimOrd (ω^⟨ a ⟩)
  add′ : ∀ a b r → LimOrd b → LimOrd ω^ a + b [ r ]

LimOrd[a]→fst[a]>𝟎 : ∀ a → LimOrd a → fst a >ᵒ 𝟎
LimOrd[a]→fst[a]>𝟎 _ (lim′ _ x)                  = x
LimOrd[a]→fst[a]>𝟎 _ (add′ _ _ (inj₁ x) lima)    = <-trans (LimOrd[a]→fst[a]>𝟎 _ lima) x
LimOrd[a]→fst[a]>𝟎 _ (add′ _ _ (inj₂ refl) lima) = LimOrd[a]→fst[a]>𝟎 _ lima

<-suc-lim′ : ∀ a b → a <ᵒ b → LimOrd b → sucₒ a <ᵒ b
<-suc-lim′ a b <₁ limb = <₂ (LimOrd[a]→fst[a]>𝟎 _ limb)
<-suc-lim′ a b (<₂ a<b) limb = <₂ a<b
<-suc-lim′ a b (<₃ refl a<b) (add′ _ _ _ limb) = <₃ refl (<-suc-lim′ _ _ a<b limb) 

⊔ₒ-idem : ∀ a → (a ⊔ₒ a) ≡ a
⊔ₒ-idem 𝟎 = refl
⊔ₒ-idem ω^ a + b [ r ] with <-tri a a 
... | inj₁ a<a = ⊥-elim (<-irrefl a<a)
... | inj₂ (inj₁ a<a) = ⊥-elim (<-irrefl a<a)
... | inj₂ (inj₂ refl) with <-tri b b 
... | inj₁ a<a = ⊥-elim (<-irrefl a<a)
... | inj₂ (inj₁ a<a) = ⊥-elim (<-irrefl a<a)
... | inj₂ (inj₂ refl) = refl

right-id : ∀ a → (a ⊔ₒ 𝟎) ≡ a
right-id 𝟎 = refl
right-id ω^ a + a₁ [ x ] = refl

⊔ₒ-<ᵒ : ∀ a b → a <ᵒ b → (a ⊔ₒ b) ≡ b
⊔ₒ-<ᵒ a b <₁            = refl
⊔ₒ-<ᵒ ω^ aa + ab [ r ] ω^ ba + bb [ s ] (<₂ x) with <-tri aa ba 
... | inj₁ x = refl
... | inj₂ (inj₁ y) = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = refl
... | inj₂ (inj₁ y) = ⊥-elim (<-irrefl x)
... | inj₂ (inj₂ refl) = refl
⊔ₒ-<ᵒ ω^ aa + ab [ r ] ω^ ba + bb [ s ] (<₃ refl x) with <-tri ba ba 
... | inj₁ x = refl
... | inj₂ (inj₁ x) = ⊥-elim (<-irrefl x)
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = refl
... | inj₂ (inj₁ y) = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
... | inj₂ (inj₂ refl) = refl

⊔ₒ-<ᵒ′ : ∀ a b → b <ᵒ a → (a ⊔ₒ b) ≡ a
⊔ₒ-<ᵒ′ a b <₁            = refl
⊔ₒ-<ᵒ′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] (<₂ x) with <-tri aa ba 
... | inj₁ y = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
... | inj₂ (inj₁ y) = refl 
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ y = ⊥-elim (<-irrefl x) 
... | inj₂ (inj₁ y) = ⊥-elim (<-irrefl x)
... | inj₂ (inj₂ refl) = MutualOrd⁼ refl refl 
⊔ₒ-<ᵒ′ ω^ aa + ab [ r ] ω^ ba + bb [ s ] (<₃ refl x) with <-tri ba ba 
... | inj₁ y = ⊥-elim (<-irrefl y)
... | inj₂ (inj₁ y) = refl 
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ y = ⊥-elim (Lm[≥→¬<] (inj₁ x) y)
... | inj₂ (inj₁ y) = refl
... | inj₂ (inj₂ refl) = MutualOrd⁼ refl refl 

<-lublub : ∀ a b c → a <ᵒ c → b <ᵒ c → (a ⊔ₒ b) <ᵒ c
<-lublub a b c <₁ b<c = b<c
<-lublub a b c a<c <₁ = subst (_<ᵒ _) (sym (right-id _)) a<c
<-lublub ω^ aa + ab [ r ] ω^ ba + bb [ s ] ω^ ca + cb [ t ] (<₂ a<c) (<₂ b<c) with <-tri aa ba
... | inj₁ x = <₂ b<c
... | inj₂ (inj₁ x) = <₂ a<c
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = <₂ b<c
... | inj₂ (inj₁ x) = <₂ a<c
... | inj₂ (inj₂ refl) = <₂ b<c
<-lublub ω^ aa + ab [ r ] ω^ ba + bb [ s ] ω^ ca + cb [ t ] (<₂ a<c) (<₃ refl b<c) with  <-tri aa ba
... | inj₁ x = <₃ refl b<c
... | inj₂ (inj₁ x) = <₂ a<c
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = <₃ refl b<c
... | inj₂ (inj₁ x) = ⊥-elim (<-irrefl a<c)
... | inj₂ (inj₂ refl) = <₃ refl b<c
<-lublub ω^ aa + ab [ r ] ω^ ba + bb [ s ] ω^ ca + cb [ t ] (<₃ refl a<c) (<₂ b<c) with <-tri aa ba
... | inj₁ x = <₂ b<c
... | inj₂ (inj₁ x) = <₃ refl a<c
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = ⊥-elim (<-irrefl b<c)
... | inj₂ (inj₁ x) = <₃ refl a<c
... | inj₂ (inj₂ refl) = ⊥-elim (<-irrefl b<c)
<-lublub ω^ aa + ab [ r ] ω^ ba + bb [ s ] ω^ ca + cb [ t ] (<₃ refl a<c) (<₃ refl b<c) with <-tri aa aa
... | inj₁ x = <₃ refl b<c
... | inj₂ (inj₁ x) = <₃ refl a<c
... | inj₂ (inj₂ refl) with <-tri ab bb
... | inj₁ x = <₃ refl b<c
... | inj₂ (inj₁ x) = <₃ refl a<c
... | inj₂ (inj₂ refl) = <₃ refl b<c

≤-lublub′ : ∀ a b c → a ≤ᵒ c → b ≤ᵒ c → (a ⊔ₒ b) ≤ᵒ c
≤-lublub′ a b c (inj₁ x) (inj₁ y) = inj₁ (<-lublub _ _ _ x y) 
≤-lublub′ a b c (inj₁ x) (inj₂ refl) = inj₂ (sym (⊔ₒ-<ᵒ _ _ x))
≤-lublub′ a b c (inj₂ refl) (inj₁ x) = inj₂ (sym (⊔ₒ-<ᵒ′ _ _ x))       
≤-lublub′ a b c (inj₂ refl) (inj₂ refl) rewrite ⊔ₒ-idem a = inj₂ refl     