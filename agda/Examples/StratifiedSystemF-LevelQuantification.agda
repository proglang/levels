
module Examples.StratifiedSystemF-LevelQuantification where
  
module Types where
  open import Level using (Level; zero; suc; _⊔_; Lift; lift)
  open import Data.Unit using (⊤; tt)
  open import Data.Nat using (ℕ) renaming (suc to sucₙ)
  open import Data.List using (List; []; _∷_)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Data.List.Relation.Unary.All using (All; [] ; _∷_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂)
  open import Function using (_∘_; id; flip; _$_)

  open import ExtendedHierarchy using (𝟎; 𝟏; ω; ω+ₙ_; ⌊_⌋; cast; β-suc-zero; β-suc-ω; β-suc-⌊⌋; ω^_+_;  <₁; <₂; <₃; ℕ→MutualOrd)
  open import BoundQuantification using (BoundLevel; BoundLift; bound-lift; bound-unlift; _,_; #; #<Λ; _<_; <₁; <₂; <₃)

  private variable
    ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : BoundLevel ⌊ ω ⌋

  module Syntax where
    LvlEnv = List ⊤

    variable
      δ δ′ δ₁ δ₂ δ₃ : LvlEnv

    data Vis : Set where
      vis : Vis
      hid : Vis

    variable
      μ μ′ μ₁ μ₂ μ₃ : Vis
    
    _⊔̌_ : Vis → Vis → Vis
    hid ⊔̌ _ = hid
    _ ⊔̌ hid = hid
    vis ⊔̌ vis = vis

    -- TODO: sort
    data Lvl (δ : LvlEnv) : Vis → Set where 
      `zero : Lvl δ vis
      `suc  : Lvl δ vis → Lvl δ vis
      `_    : ∀ {l} → l ∈ δ → Lvl δ vis
      _`⊔_  : Lvl δ μ₁ → Lvl δ μ₂ → Lvl δ (μ₁ ⊔̌ μ₂)
      `ω+_  : ℕ → Lvl δ hid
      
    variable
      l l′ l₁ l₂ l₃ : Lvl δ vis
    
    wkₗ  : Lvl δ μ → Lvl (tt ∷ δ) μ
    wkₗ `zero      = `zero
    wkₗ (`suc l)   = `suc (wkₗ l)
    wkₗ (` x)      = ` (there x)
    wkₗ (l₁ `⊔ l₂) = wkₗ l₁ `⊔ wkₗ l₂
    wkₗ (`ω+ n)    = `ω+ n

    Env : LvlEnv → Set
    Env δ = List (Lvl δ vis)
  
    wkₗₑ : Env δ → Env (tt ∷ δ)
    wkₗₑ []      = []
    wkₗₑ (l ∷ Δ) = wkₗ l ∷ wkₗₑ Δ
      
    variable
      Δ Δ′ Δ₁ Δ₂ Δ₃ : Env δ
    
    data Type (δ : LvlEnv) (Δ : Env δ) : Lvl δ μ → Set where
      Nat   : Type δ Δ `zero
      `_    : l ∈ Δ → Type δ Δ l
      _⇒_   : Type δ Δ l₁ → Type δ Δ l₂ → Type δ Δ (l₁ `⊔ l₂) 
      ∀α    : (l : Lvl δ vis) → Type δ (l ∷ Δ) l′ → Type δ Δ (`suc l `⊔ l′) 
      ∀ℓ    : Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ l) → Type δ Δ ((`ω+ 0) `⊔ l)
      Ty    : (l : Lvl δ vis) → Type δ Δ (`suc l)
      Tyω+_ : (n : ℕ) → Type δ Δ (`ω+ sucₙ n)
      
    pattern ∀α:_⇒_ l {l′ = l′} T = ∀α {l = l} {l′ = l′} T

  module Denotational where
    open Syntax 
    ⟦_⟧ηₗ : (δ : LvlEnv) → Set
    ⟦_⟧ηₗ δ = tt ∈ δ → Level
    
    []ηₗ : ⟦ [] ⟧ηₗ
    []ηₗ ()

    _∷ηₗ_ : ∀ {δ : LvlEnv} → (BoundLevel ⌊ ω ⌋) → ⟦ δ ⟧ηₗ → ⟦ tt ∷ δ ⟧ηₗ
    (l ∷ηₗ ηₗ) (here refl) = # l
    (l ∷ηₗ ηₗ) (there x) = ηₗ x

    lookupηₗ : ∀ {δ : LvlEnv} → ⟦ δ ⟧ηₗ → tt ∈ δ → Level 
    lookupηₗ ηₗ x = ηₗ x

    ⟦_⟧ₗ : ∀ {δ : LvlEnv} → (l : Lvl δ μ) → ⟦ δ ⟧ηₗ → Level
    ⟦ `zero    ⟧ₗ ηₗ = zero
    ⟦ `suc l   ⟧ₗ ηₗ = suc (⟦ l ⟧ₗ  ηₗ)
    ⟦ ` x      ⟧ₗ ηₗ = lookupηₗ ηₗ x
    ⟦ l₁ `⊔ l₂ ⟧ₗ ηₗ = ⟦ l₁ ⟧ₗ ηₗ ⊔ ⟦ l₂ ⟧ₗ ηₗ
    ⟦ `ω+ n ⟧ₗ ηₗ    = ⌊ ω+ₙ n ⌋
    
    suc⨆ :  {δ : LvlEnv} → ⟦ δ ⟧ηₗ → Env δ → Level
    suc⨆ ηₗ [] = zero
    suc⨆ ηₗ (l ∷ Δ) = suc (⟦ l ⟧ₗ ηₗ) ⊔ suc⨆ ηₗ Δ  

    l∈Δ⇒l<⨆Δ : {δ : LvlEnv} {Δ : Env δ} {l : Lvl δ vis} (ηₗ : ⟦ δ ⟧ηₗ) → l ∈ Δ → ⟦ l ⟧ₗ ηₗ < (suc⨆ ηₗ Δ)
    l∈Δ⇒l<⨆Δ {Δ = Δ} ηₗ (here refl) = <₃ {ℓ₂ = suc⨆ ηₗ Δ} <₁
    l∈Δ⇒l<⨆Δ {Δ = Δ} ηₗ (there x) = <₃ {ℓ₂ = suc⨆ ηₗ Δ} (l∈Δ⇒l<⨆Δ ηₗ x)
  
    ⟦⟧ₗ-wk : {δ : LvlEnv} (ηₗ : ⟦ δ ⟧ηₗ) (l : Lvl δ μ) (ℓ : BoundLevel ⌊ ω ⌋) → ⟦ wkₗ l ⟧ₗ (ℓ ∷ηₗ ηₗ) ≡ ⟦ l ⟧ₗ ηₗ
    ⟦⟧ₗ-wk ηₗ `zero      ℓ = refl
    ⟦⟧ₗ-wk ηₗ (`suc l)   ℓ = cong suc (⟦⟧ₗ-wk ηₗ l ℓ)
    ⟦⟧ₗ-wk ηₗ (` x)      ℓ = lookup-wk ηₗ x ℓ
      where lookup-wk : ∀  {δ : LvlEnv} (ηₗ : ⟦ δ ⟧ηₗ) x ℓ → lookupηₗ (ℓ ∷ηₗ ηₗ) (there x) ≡ lookupηₗ ηₗ x
            lookup-wk {tt ∷ []}     ηₗ t ℓ = refl
            lookup-wk {tt ∷ tt ∷ δ} ηₗ t ℓ = refl
    ⟦⟧ₗ-wk ηₗ (l₁ `⊔ l₂) ℓ = cong₂ _⊔_ (⟦⟧ₗ-wk ηₗ l₁ ℓ) (⟦⟧ₗ-wk ηₗ l₂ ℓ)
    ⟦⟧ₗ-wk ηₗ (`ω+ x)    ℓ = refl

    ⟦_⟧η_ : (Δ : Env δ) → (ηₗ : ⟦ δ ⟧ηₗ) → Set (suc⨆ ηₗ Δ)
    ⟦_⟧η_ {δ = δ} Δ ηₗ = ∀ (l : Lvl δ vis) → (x : l ∈ Δ) → BoundLift (l∈Δ⇒l<⨆Δ ηₗ x) (Set (⟦ l ⟧ₗ ηₗ)) 

    []η : (ηₗ : ⟦ δ ⟧ηₗ) → ⟦ [] ⟧η ηₗ 
    []η _ _ ()
    
    _∷η_   : {Δ : Env δ} → {ηₗ : ⟦ δ ⟧ηₗ} → Set (⟦ l ⟧ₗ ηₗ) → ⟦ Δ ⟧η ηₗ → ⟦ l ∷ Δ ⟧η ηₗ
    (_∷η_) {l = l} {ηₗ = ηₗ} A η (.l) x@(here refl) = bound-lift (l∈Δ⇒l<⨆Δ {l = l} ηₗ x) A
    (_∷η_) {l = l} {ηₗ = ηₗ} A η l′ x@(there x′)    = bound-lift (l∈Δ⇒l<⨆Δ {l = l′} ηₗ x) (bound-unlift (l∈Δ⇒l<⨆Δ _ _) (η _ x′))
    
    _∷η⋆_ : {Δ : Env δ} → {ηₗ : ⟦ δ ⟧ηₗ} → (ℓ : BoundLevel ⌊ ω ⌋) → ⟦ Δ ⟧η ηₗ → ⟦ wkₗₑ Δ ⟧η (ℓ ∷ηₗ ηₗ)
    _∷η⋆_ {δ} {Δ = l₁ ∷ Δ} ℓ η l (here refl) = {! η _ (here refl)  !}
    _∷η⋆_ {δ} {Δ = l₁ ∷ l₂ ∷ Δ} ℓ η l (there x) = {!   !}

    lookup : {Δ : Env δ} {ηₗ : ⟦ δ ⟧ηₗ} → ⟦ Δ ⟧η ηₗ → l ∈ Δ → Set (⟦ l ⟧ₗ ηₗ)
    lookup η x = bound-unlift (l∈Δ⇒l<⨆Δ _ _) (η _ x) 

    ⟦_⟧ : ∀ {δ : LvlEnv} {l : Lvl δ μ} {Δ : Env δ} → (T : Type δ Δ l) (ηₗ : ⟦ δ ⟧ηₗ) → ⟦ Δ ⟧η ηₗ → Set (⟦ l ⟧ₗ ηₗ)
    ⟦ Nat     ⟧ ηₗ η = ℕ
    ⟦ ` α     ⟧ ηₗ η = lookup η α
    ⟦ T₁ ⇒ T₂ ⟧ ηₗ η = ⟦ T₁ ⟧ ηₗ η → ⟦ T₂ ⟧ ηₗ η 
    ⟦ ∀α l T  ⟧ ηₗ η = ∀ A → ⟦ T ⟧ ηₗ (A ∷η η) 
    ⟦_⟧ {l = l} (∀ℓ T) ηₗ η = ∀ (ℓ : BoundLevel ⌊ ω ⌋) → cast (⟦⟧ₗ-wk ηₗ l ℓ) (Lift ⌊ ω ⌋ (⟦ T ⟧ (ℓ ∷ηₗ ηₗ) (ℓ ∷η⋆ η)))
    ⟦ Ty l    ⟧ ηₗ η = Set (⟦ l ⟧ₗ ηₗ) 
    ⟦ Tyω+ n  ⟧ ηₗ η = cast β-red (Set ⌊ ω+ₙ n ⌋)
      where β-red = trans (β-suc-ω {ℓ₁ = ⌊ 𝟏 ⌋} {ℓ₂ = ⌊ ℕ→MutualOrd n ⌋})
                          (cong (ω^ ⌊ 𝟏 ⌋ +_) (β-suc-⌊⌋ {ℕ→MutualOrd n}))
          