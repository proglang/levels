module Level2 where
  
open import Agda.Builtin.Equality using (_≡_; refl)
open import Level public

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  Λ Λ′ Λ₁ Λ₂ Λ₃ Λ₄ : Level

cast : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≡ ℓ₂ → Set ℓ₁ → Set ℓ₂ 
cast refl A = A

module ExtendedHierarchy where

  Setε₀ = Setω

  infix 40 ω↑_+_
  -- should be a private postulate but we keep it public
  -- so we can prove level equalities that would in normally be solved by the compiler
  postulate
    ω↑_+_ : (ℓ₁ ℓ₂ : Level) → Level

  postulate
    -- by definition
    β-suc-zero : suc zero ≡ ω↑ zero + zero
    β-suc-ω    : suc (ω↑ ℓ₁ + ℓ₂) ≡ ω↑ ℓ₁ + suc ℓ₂

    -- see ???
    distributivity : ω↑ ℓ + (ℓ₁ ⊔ ℓ₂) ≡ ω↑ ℓ + ℓ₁ ⊔ ω↑ ℓ + ℓ₂ 

    subsumption₁₀ : ℓ ⊔ ω↑ ℓ₁ + ℓ ≡ ω↑ ℓ₁ + ℓ
    subsumption₁₁ : ℓ ⊔ ω↑ ℓ₁ + suc ℓ ≡ ω↑ ℓ₁ + suc ℓ
    subsumption₁₂ : ℓ ⊔ ω↑ ℓ₁ + suc (suc ℓ) ≡ ω↑ ℓ₁ + suc (suc ℓ)

    subsumption₂₀ : ℓ ⊔ ω↑ ℓ₁ + ω↑ ℓ₂ + ℓ ≡ ω↑ ℓ₁ + ω↑ ℓ₂ + ℓ
    subsumption₂₁ : ℓ ⊔ ω↑ ℓ₁ + ω↑ ℓ₂ + suc ℓ ≡ ω↑ ℓ₁ + ω↑ ℓ₂ + suc ℓ
    subsumption₂₂ : ℓ ⊔ ω↑ ℓ₁ + ω↑ ℓ₂ + suc (suc ℓ) ≡ ω↑ ℓ₁ + ω↑ ℓ₂ + suc (suc ℓ)

    -- ...


  -- compatibility 
  open import Ordinal public
  ⌊_⌋ : MutualOrd → Level
  ⌊ 𝟎 ⌋                = zero
  ⌊ ω^ l₁ + l₂ [ _ ] ⌋ = ω↑ ⌊ l₁ ⌋ + ⌊ l₂ ⌋

  module Laws where
    

module BoundedQuantification where
  -- open ExtendedHierarchy hiding (_<_; <₁; <₂; <₃)
   
  data _<_ : Level → Level → Set where
    <₁ : ℓ < suc ℓ
    <₂ : ℓ₁ < ℓ₂ → ℓ₁ < suc ℓ₂
    <₃ : ℓ < ℓ₁ → ℓ < (ℓ₁ ⊔ ℓ₂)
    -- <ₑ : ∀ {l₁ l₂} →  l₁ ExtendedHierarchy.< l₂ → ⟦ l₁ ⟧ < ⟦ l₂ ⟧
  
  record BoundLevel (Λ : Level) : Set Λ where
    constructor _,_  
    field 
      level : Level
      ℓ<Λ : level < Λ
  
  open BoundLevel public

  bound : BoundLevel Λ → Level
  bound {Λ} _ = Λ

  BoundLift  : ∀ (l : BoundLevel Λ) → Set (suc (level l)) → Set Λ
  BoundLift (ℓ , <₁)                         A = Lift (suc ℓ) A
  BoundLift (ℓ , <₂ {ℓ₂ = ℓ₂} ℓ<Λ)           A = Lift {a = ℓ₂} _ (BoundLift (ℓ , ℓ<Λ) A)
  BoundLift (ℓ , <₃ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂} ℓ<Λ) A = Lift {a = ℓ₁} ℓ₂ (BoundLift (ℓ , ℓ<Λ) A)

  bound-lift : ∀ (l : BoundLevel Λ) → Set (level l) → BoundLift l (Set (level l))
  bound-lift (level , <₁)     A = lift A
  bound-lift (level , <₂ ℓ<Λ) A = lift (bound-lift (level , ℓ<Λ) A)
  bound-lift (level , <₃ ℓ<Λ) A = lift (bound-lift (level , ℓ<Λ) A)

  bound-unlift : ∀ (l : BoundLevel Λ) → BoundLift l (Set (level l)) → Set (level l)
  bound-unlift (level , <₁)     (Level.lift A) = A
  bound-unlift (level , <₂ ℓ<Λ) (Level.lift A) = bound-unlift ((level , ℓ<Λ)) A
  bound-unlift (level , <₃ ℓ<Λ) (Level.lift A) = bound-unlift ((level , ℓ<Λ)) A

  module BoundedExtendedHierarchy where
    -- BoundLiftExtended : {a b : MutualOrd} → a ExtendedHierarchy.< b → Set ⟦ a ⟧ → Set ⟦ b ⟧
    -- BoundLiftExtended {a} {b} ExtendedHierarchy.<₁         A = Lift ⟦ b ⟧ A
    -- BoundLiftExtended {ω^ a + b [ r ]} {ω^ c + d [ s ]} (ExtendedHierarchy.<₂ a<b) A = {! A  !}
    -- BoundLiftExtended {a} {b} (ExtendedHierarchy.<₃ x a<b) A = {!   !}

  module Properties where
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    
    inverse-property : ∀ (l : BoundLevel Λ) (A : Set (level l)) → bound-unlift l (bound-lift l A) ≡ A 
    inverse-property (ℓ , <₁)     A = refl
    inverse-property (ℓ , <₂ ℓ<Λ) A = inverse-property (ℓ , ℓ<Λ) A
    inverse-property (ℓ , <₃ ℓ<Λ) A = inverse-property (ℓ , ℓ<Λ) A
