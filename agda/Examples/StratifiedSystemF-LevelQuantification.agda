
module Examples.StratifiedSystemF-LevelQuantification where
  
module Types where
  open import Level using (Level; zero; suc; _⊔_)
  open import Data.Unit using (⊤; tt)
  open import Data.Nat using (ℕ)
  open import Data.List using (List; []; _∷_)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Data.List.Relation.Unary.All using (All; [] ; _∷_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
  open import Function using (_∘_; id; flip; _$_)

  open import ExtendedHierarchy using (𝟎; 𝟏; ω; ω+ₙ_; ⌊_⌋; cast; β-suc-zero; β-suc-ω; ω^_+_; <₁; <₂; <₃)
  open import BoundQuantification using (BoundLevel; BoundLift; bound-lift; bound-unlift; _,_; #; #<Λ; _<_; <₁; <₂; <₃)

  private variable
    ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : BoundLevel ⌊ ω ⌋

  module Syntax where
    LvlEnv = List ⊤

    variable
      δ δ′ δ₁ δ₂ δ₃ : LvlEnv

    data Lvl (δ : LvlEnv) : Set where 
      `zero : Lvl δ 
      `suc  : Lvl δ → Lvl δ
      `_    : ∀ {l} → l ∈ δ → Lvl δ 
      ♯     : (l : BoundLevel ⌊ ω ⌋) → Lvl δ
      _`⊔_  : Lvl δ → Lvl δ → Lvl δ
      `ω+_  : ℕ → Lvl δ
      
    variable
      l l′ l₁ l₂ l₃ : Lvl δ

    Env : LvlEnv → Set
    Env δ = List (Lvl δ)

    postulate 
      wkₗ  : Lvl δ → Lvl (tt ∷ δ) 
      wkₗₑ : Env δ → Env (tt ∷ δ)
      
    variable
      Δ Δ′ Δ₁ Δ₂ Δ₃ : Env δ
    
    data Type (δ : LvlEnv) (Δ : Env δ) : Lvl δ → Set where
      Nat   : Type δ Δ `zero
      `_    : l ∈ Δ → Type δ Δ l
      _⇒_   : Type δ Δ l₁ → Type δ Δ l₂ → Type δ Δ (l₁ `⊔ l₂) 
      ∀α    : (l : Lvl δ) → Type δ (l ∷ Δ) l′ → Type δ Δ (`suc l `⊔ l′) 
      ∀ℓ    : Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ l) → Type δ Δ l
      Ty    : (l : Lvl δ) → Type δ Δ (`suc l)
      Tyω+_ : (n : ℕ) → Type δ Δ (`suc (`ω+ n))
      
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

    ⟦_⟧ₗ : ∀ {δ : LvlEnv} → (l : Lvl δ) → ⟦ δ ⟧ηₗ → Level
    ⟦ `zero    ⟧ₗ ηₗ = zero
    ⟦ `suc l   ⟧ₗ ηₗ = suc (⟦ l ⟧ₗ  ηₗ)
    ⟦ ` x      ⟧ₗ ηₗ = lookupηₗ ηₗ x
    ⟦ ♯ l      ⟧ₗ ηₗ = # l
    ⟦ l₁ `⊔ l₂ ⟧ₗ ηₗ = ⟦ l₁ ⟧ₗ ηₗ ⊔ ⟦ l₂ ⟧ₗ ηₗ
    ⟦ `ω+ n ⟧ₗ ηₗ    = ⌊ ω+ₙ n ⌋
    
    suc⨆ :  {δ : LvlEnv} → ⟦ δ ⟧ηₗ → Env δ → Level
    suc⨆ ηₗ [] = zero
    suc⨆ ηₗ (l ∷ Δ) = suc (⟦ l ⟧ₗ ηₗ) ⊔ suc⨆ ηₗ Δ  

    l∈Δ⇒l<⨆Δ : {δ : LvlEnv} {Δ : Env δ} {l : Lvl δ} (ηₗ : ⟦ δ ⟧ηₗ) → l ∈ Δ → ⟦ l ⟧ₗ ηₗ < (suc⨆ ηₗ Δ)
    l∈Δ⇒l<⨆Δ {Δ = Δ} ηₗ (here refl) = <₃ {ℓ₂ = suc⨆ ηₗ Δ} <₁
    l∈Δ⇒l<⨆Δ {Δ = Δ} ηₗ (there x) = <₃ {ℓ₂ = suc⨆ ηₗ Δ} (l∈Δ⇒l<⨆Δ ηₗ x)
    
    postulate
      ⟦⟧ₗ-wk : {δ : LvlEnv} (ηₗ : ⟦ δ ⟧ηₗ) (l : Lvl δ) → ⟦ wkₗ l ⟧ₗ (ℓ ∷ηₗ ηₗ) ≡ ⟦ l ⟧ₗ ηₗ

    ⟦_⟧η_ : (Δ : Env δ) → (ηₗ : ⟦ δ ⟧ηₗ) → Set (suc⨆ ηₗ Δ)
    ⟦_⟧η_ {δ = δ} Δ ηₗ = ∀ (l : Lvl δ) → (x : l ∈ Δ) → BoundLift (l∈Δ⇒l<⨆Δ ηₗ x) (Set (⟦ l ⟧ₗ ηₗ)) 

    []η : (ηₗ : ⟦ δ ⟧ηₗ) → ⟦ [] ⟧η ηₗ 
    []η _ _ ()
    
    _∷η_   : {Δ : Env δ} → {ηₗ : ⟦ δ ⟧ηₗ} → Set (⟦ l ⟧ₗ ηₗ) → ⟦ Δ ⟧η ηₗ → ⟦ l ∷ Δ ⟧η ηₗ
    (_∷η_) {l = l} {ηₗ = ηₗ} A η (.l) x@(here refl) = bound-lift (l∈Δ⇒l<⨆Δ {l = l} ηₗ x) A
    (_∷η_) {l = l} {ηₗ = ηₗ} A η l′ x@(there x′)    = bound-lift (l∈Δ⇒l<⨆Δ {l = l′} ηₗ x) (bound-unlift (l∈Δ⇒l<⨆Δ _ _) (η _ x′))
    
    postulate 
      _∷η⋆_ : {Δ : Env δ} → {ηₗ : ⟦ δ ⟧ηₗ} → (ℓ : BoundLevel ⌊ ω ⌋) → ⟦ Δ ⟧η ηₗ → ⟦ wkₗₑ Δ ⟧η (ℓ ∷ηₗ ηₗ)

    lookup : {Δ : Env δ} {ηₗ : ⟦ δ ⟧ηₗ} → ⟦ Δ ⟧η ηₗ → l ∈ Δ → Set (⟦ l ⟧ₗ ηₗ)
    lookup η x = bound-unlift (l∈Δ⇒l<⨆Δ _ _) (η _ x) 
    
    ⟦_⟧ : ∀ {δ : LvlEnv} {l : Lvl δ} {Δ : Env δ} → (T : Type δ Δ l) (ηₗ : ⟦ δ ⟧ηₗ) → ⟦ Δ ⟧η ηₗ → Set (⟦ l ⟧ₗ ηₗ)
    ⟦ Nat     ⟧ ηₗ η = ℕ
    ⟦ ` α     ⟧ ηₗ η = lookup η α
    ⟦ T₁ ⇒ T₂ ⟧ ηₗ η = ⟦ T₁ ⟧ ηₗ η → ⟦ T₂ ⟧ ηₗ η 
    ⟦ ∀α l T  ⟧ ηₗ η = ∀ A → ⟦ T ⟧ ηₗ (A ∷η η) 
    ⟦_⟧ {l = l} (∀ℓ T) ηₗ η = ∀ (ℓ : BoundLevel ⌊ ω ⌋) → cast (⟦⟧ₗ-wk {ℓ = ℓ} ηₗ l) (⟦ T ⟧ (ℓ ∷ηₗ ηₗ) (ℓ ∷η⋆ η)) 
    ⟦ Ty l    ⟧ ηₗ η = Set (⟦ l ⟧ₗ ηₗ) 
    ⟦ Tyω+ n  ⟧ ηₗ η = Set ⌊ ω+ₙ n ⌋
         