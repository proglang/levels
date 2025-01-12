module CNF-example where
  open import Relation.Binary.Definitions using (Irreflexive)
  open import Induction using (RecStruct)
  open import Induction.WellFounded using (WellFounded; WfRec)

  data CNF : Set
  data _<_ : CNF → CNF → Set
  ↑_ : CNF → CNF
  
  _>_ _≥_ _≤_ : CNF → CNF → Set
  α > β = β < α
  α ≥ β = α > β ⊎ α ≡ β
  α ≤ β = β ≥ α


  data CNF where
    𝟎 : CNF
    ω^_+_[_] : (α β : CNF) → α ≥ (↑ β) → CNF
  
  variable
    α β γ δ : CNF
    α≥↑β : α ≥ (↑ β)
    γ≥↑δ : γ ≥ (↑ δ)
  
  data _<_ where
   <₁ : 𝟎 < ω^ α + β [ α≥↑β ]
   <₂ : α < γ → ω^ α + β [ α≥↑β ] < ω^ γ + δ [ γ≥↑δ ]
   <₃ : α ≡ γ → β < δ → ω^ α + β [ α≥↑β ] < ω^ γ + δ [ γ≥↑δ ]
  
  ↑ 𝟎                = 𝟎
  ↑ (ω^ α + _ [ _ ]) = α 

  <-transitivity : β < γ → α < β → α < γ 
  <-transitivity (<₂ _)        <₁            = <₁
  <-transitivity (<₃ _ _)      <₁            = <₁
  <-transitivity (<₂ β<γ)      (<₂ α<β)      = <₂ (<-transitivity β<γ α<β)
  <-transitivity (<₃ refl _)   (<₂ α<γ)      = <₂ α<γ
  <-transitivity (<₂ α<γ)      (<₃ refl _)   = <₂ α<γ
  <-transitivity (<₃ refl β<γ) (<₃ refl α<β) = <₃ refl (<-transitivity β<γ α<β)

  <-irreflexive : Irreflexive _≡_ _<_
  <-irreflexive refl (<₂ α<α)      = <-irreflexive refl α<α
  <-irreflexive refl (<₃ refl α<α) = <-irreflexive refl α<α

  <-irrelevant : (α<β₁ α<β₂ : α < β) → α<β₁ ≡ α<β₂
  <-irrelevant <₁             <₁             = refl
  <-irrelevant (<₂ α<β₁)      (<₂ α<β₂)      = cong <₂ (<-irrelevant α<β₁ α<β₂)
  <-irrelevant (<₂ α<β₁)      (<₃ refl α<β₂) = ⊥-elim (<-irreflexive refl α<β₁)
  <-irrelevant (<₃ refl α<β₁) (<₂ α<β₂)      = ⊥-elim (<-irreflexive refl α<β₂)
  <-irrelevant (<₃ refl α<β₁) (<₃ refl α<β₂) = cong (<₃ refl) (<-irrelevant α<β₁ α<β₂)

  --module Lex {A : Set a} {B : A → Set b}
  --                   (RelA : Rel A ℓ₁)
  --                   (RelB : ∀ x → Rel (B x) ℓ₂) where
  --                   
  --  infix 4 _<_
  --  data _<_ : Rel (Σ A B) (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  --    left  : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : RelA   x₁ x₂) → (x₁ , y₁) < (x₂ , y₂)
  --    right : ∀ {x y₁ y₂}     (y₁<y₂ : RelB x y₁ y₂) → (x  , y₁) < (x  , y₂)
--
  --  mutual
--
  --    accessible : ∀ {x y} →
  --                 Acc RelA x → (∀ {x} → WellFounded (RelB x)) →
  --                 Acc _<_ (x , y)
  --    accessible accA wfB = acc (accessible′ accA (wfB _) wfB)
--
--
  --    accessible′ :
  --      ∀ {x y} →
  --      Acc RelA x → Acc (RelB x) y → (∀ {x} → WellFounded (RelB x)) →
  --      WfRec _<_ (Acc _<_) (x , y)
  --    accessible′ (acc rsA) _    wfB (left  x′<x) = accessible (rsA x′<x) wfB
  --    accessible′ accA (acc rsB) wfB (right y′<y) =
  --      acc (accessible′ accA (rsB y′<y) wfB)
--
  --    wellFounded : WellFounded RelA → (∀ {x} → WellFounded (RelB x)) →
  --                  WellFounded _<_
  --    wellFounded wfA wfB p = accessible (wfA (proj₁ p)) wfB
--
  --    well-founded = wellFounded

   

  <-Rec : ∀{ℓ} → RecStruct CNF ℓ ℓ
  <-Rec = WfRec _<_

  postulate
    <-wellFounded : WellFounded _<_
    <-wellFounded′ : ∀ α → <-Rec (Acc _<_) α

  -- <-wellFounded n = acc (<-wellFounded′ n)

  -- <-wellFounded′ ω^ γ + δ [ γ≥↑δ ] <₁            = acc λ { () }
  -- <-wellFounded′ ω^ γ + δ [ γ≥↑δ ] (<₂ {α = α} {β = β} {α≥↑β = α≥↑β} α<γ) with <-wellFounded′ γ α<γ 
  -- ... | a = {!   !} -- with <-wellFounded′ α γ<α 
  -- -- ... | hjkl = acc λ x → <-wellFounded′ (↑ β) {!   !} 
  -- <-wellFounded′ ω^ γ + δ [ γ≥↑δ ] (<₃ refl β<δ) = {!   !}

  lvl : LvlStruct
  lvl = record {
      Lvl    = CNF
    ; _<_    = _<_
    ; <-prop = <-irrelevant _ _
    ; _∘_    = <-transitivity
    ; wf     = <-wellFounded _
    }
    
  open IR-Universe lvl hiding (_<_)
  
  postulate
    <-compare : (α β : CNF) → (α < β) ⊎ (β < α) ⊎ α ≡ β
  -- <-compare 𝟎                 𝟎                 = inj₂ (inj₂ refl)
  -- <-compare 𝟎                 ω^ _ + _ [ _ ]    = inj₁ <₁
  -- <-compare ω^ _ + _ [ _ ]    𝟎                 = inj₂ (inj₁ <₁)
  -- <-compare ω^ α + β [ α≥↑β ] ω^ γ + δ [ γ≥↑δ ] with <-compare α γ 
  -- ... | inj₁ α<γ         = inj₁ (<₂ α<γ)
  -- ... | inj₂ (inj₁ γ<α)  = inj₂ (inj₁ (<₂ γ<α))
  -- ... | inj₂ (inj₂ refl) with <-compare β δ 
  -- ... | inj₁ β<δ         = inj₁ (<₃ refl β<δ)
  -- ... | inj₂ (inj₁ δ<β)  = inj₂ (inj₁ (<₃ refl δ<β))
  -- ... | inj₂ (inj₂ refl) = {!   !} -- todo α≥↑β proof is unique 

    <-extensional : {α β : CNF} → ((γ : CNF) → (γ < α → γ < β) × (γ < β → γ < α)) → α ≡ β
  -- <-extensional = {!   !}
  
  ord : Ordinal lvl
  ord = record { 
      cmp   = <-compare 
    ; <-ext = <-extensional 
    } 
    
  open IR-Univ-Ordinal ord 