module Examples.SSF where

open import Level using (Level; zero; suc; _⊔_)
open import Data.Nat using (ℕ) 
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_) 
open import Data.List.Relation.Unary.Any using (here; there)

module Types where 
  open import Data.List.Relation.Unary.All using (All; [] ; _∷_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Function using (_∘_; id; flip; _$_)

  variable
    ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Level

  module Syntax where

    module Environment where
      Env = List Level

      variable
        Δ Δ′ Δ₁ Δ₂ Δ₃ : Env

      suc⨆Δ_ : Env → Level
      suc⨆Δ []       = zero
      suc⨆Δ (ℓ ∷ ℓs) = suc ℓ ⊔ suc⨆Δ ℓs
    
    open Environment
    
    data Type (Δ : Env) : Level → Set where
      Nat : Type Δ zero
      `_  : ℓ ∈ Δ → Type Δ ℓ
      _⇒_ : Type Δ ℓ₁ → Type Δ ℓ₂ → Type Δ (ℓ₁ ⊔ ℓ₂)
      ∀α  : Type (ℓ ∷ Δ) ℓ′ → Type Δ (suc ℓ ⊔ ℓ′)
    pattern ∀α:_⇒_ ℓ {ℓ′ = ℓ′} T = ∀α {ℓ = ℓ} {ℓ′ = ℓ′} T

    variable
      T T′ T₁ T₂ T₃ : Type Δ ℓ

  module Substitution where
    open Syntax   
    open Syntax.Environment
      
    REN : (Δ₁ Δ₂ : Env) → Set
    REN Δ₁ Δ₂ = ∀ {ℓ} → ℓ ∈ Δ₁ → ℓ ∈ Δ₂

    module _ (ρ : REN (ℓ ∷ Δ₁) Δ₂) where
      popᵣ : REN Δ₁ Δ₂
      popᵣ = ρ ∘ there

      topᵣ : ℓ ∈ Δ₂
      topᵣ = ρ (here refl)

    tabulateᵣ : REN Δ₁ Δ₂ → All (_∈ Δ₂) Δ₁
    tabulateᵣ {Δ₁ = []}    _ = []
    tabulateᵣ {Δ₁ = _ ∷ _} ρ = topᵣ ρ ∷ tabulateᵣ (popᵣ ρ)

    lookupᵣ : All (_∈ Δ₂) Δ₁ → REN Δ₁ Δ₂
    lookupᵣ (α ∷ ρ) = λ where (here refl) → α ; (there x) → lookupᵣ ρ x

    record Ren (Δ₁ Δ₂ : Env) : Set where
      constructor mkRen
      field
        renᵣ : REN Δ₁ Δ₂

      TR-level : Level
      TR-level = (suc⨆Δ Δ₁) ⊔ (suc⨆Δ Δ₂)

      wkᵣ : REN Δ₁ (ℓ ∷ Δ₂)
      wkᵣ = there ∘ renᵣ

      liftᵣ : REN (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)
      liftᵣ (here refl) = (here refl)
      liftᵣ (there α)   = there $ renᵣ α

    open Ren public using (renᵣ)

    module _ (ρ : Ren Δ₁ Δ₂) where
      wkᵣ : Ren Δ₁ (ℓ ∷ Δ₂)
      renᵣ wkᵣ = Ren.wkᵣ ρ

      liftᵣ : Ren (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)
      renᵣ liftᵣ = Ren.liftᵣ ρ


    private variable
      ρ ρ′ ρ₁ ρ₂ ρ₃ : Ren Δ₁ Δ₂

    idᵣ : Ren Δ Δ
    renᵣ idᵣ = id

    skipᵣ : Ren Δ (ℓ ∷ Δ)
    renᵣ skipᵣ = there

    dropᵣ : Ren (ℓ ∷ Δ₁) Δ₂ → Ren Δ₁ Δ₂
    renᵣ (dropᵣ ρ*) = popᵣ $ renᵣ ρ*

    ren : Ren Δ₁ Δ₂ → Type Δ₁ ℓ → Type Δ₂ ℓ
    ren ρ (` α)     = ` renᵣ ρ α
    ren ρ (T₁ ⇒ T₂) = ren ρ T₁ ⇒ ren ρ T₂
    ren ρ (∀α T)    = ∀α (ren (liftᵣ ρ) T)
    ren ρ Nat       = Nat

    ⟦_⟧ᵣ_ : Type Δ₁ ℓ → Ren Δ₁ Δ₂ → Type Δ₂ ℓ
    ⟦_⟧ᵣ_ = flip ren

    wk : Type Δ ℓ′ → Type (ℓ ∷ Δ) ℓ′
    wk = ren skipᵣ

    SUB : (Δ₁ Δ₂ : Env) → Set
    SUB Δ₁ Δ₂ = ∀ {l} → l ∈ Δ₁ → Type Δ₂ l

    module _ (σ : SUB (ℓ ∷ Δ₁) Δ₂) where
      popₛ : SUB Δ₁ Δ₂
      popₛ = σ ∘ there

      topₛ : Type Δ₂ ℓ
      topₛ = σ (here refl)

    tabulateₛ : SUB Δ₁ Δ₂ → All (Type Δ₂) Δ₁
    tabulateₛ {Δ₁ = []}    _ = []
    tabulateₛ {Δ₁ = _ ∷ _} σ = topₛ σ ∷ tabulateₛ (popₛ σ)

    lookupₛ : All (Type Δ₂) Δ₁ → SUB Δ₁ Δ₂
    lookupₛ (α ∷ σ) = λ where (here refl) → α ; (there x) → lookupₛ σ x

    record Sub (Δ₁ Δ₂ : Env) : Set where
      constructor mkSub
      field
        subₛ : SUB Δ₁ Δ₂

      TS-level : Level
      TS-level = (suc⨆Δ Δ₁) ⊔ (suc⨆Δ Δ₂)

      wkₛ : SUB Δ₁ (ℓ ∷ Δ₂)
      wkₛ = wk ∘ subₛ

      liftₛ : SUB (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)
      liftₛ (here refl)      = ` (here refl)
      liftₛ (there α) = wk $ subₛ α

      extₛ : Type Δ₂ ℓ → SUB (ℓ ∷ Δ₁) Δ₂
      extₛ T (here refl) = T
      extₛ T (there α)   = subₛ α


    open Sub public using (subₛ)

    module _ (σ : Sub Δ₁ Δ₂) where
      wkₛ : Sub Δ₁ (ℓ ∷ Δ₂)
      subₛ wkₛ = Sub.wkₛ σ

      liftₛ : Sub (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)
      subₛ liftₛ = Sub.liftₛ σ

      extₛ : Type Δ₂ ℓ → Sub (ℓ ∷ Δ₁) Δ₂
      subₛ (extₛ T) = Sub.extₛ σ T


    private variable
      σ σ′ σ₁ σ₂ σ₃ : Sub Δ₁ Δ₂

    idₛ : Sub Δ Δ

    subₛ idₛ = `_

    sub : Sub Δ₁ Δ₂ → Type Δ₁ ℓ → Type Δ₂ ℓ
    sub σ (` α)     = subₛ σ α
    sub σ (T₁ ⇒ T₂) = sub σ T₁ ⇒ sub σ T₂
    sub σ (∀α T)    = ∀α (sub (liftₛ σ) T)
    sub σ Nat       = Nat

    ⟦_⟧ₛ_ : Type Δ₁ ℓ → Sub Δ₁ Δ₂ → Type Δ₂ ℓ
    ⟦_⟧ₛ_ = flip sub

    _∷ₛ_ : Type Δ₂ ℓ → Sub Δ₁ Δ₂ → Sub (ℓ ∷ Δ₁) Δ₂
    T ∷ₛ σ = extₛ σ T

    [_]ₛ : Type Δ ℓ → Sub (ℓ ∷ Δ) Δ
    [ T ]ₛ = T ∷ₛ idₛ

    _[_] : Type (ℓ ∷ Δ) ℓ′ → Type Δ ℓ → Type Δ ℓ′
    _[_] T T' = ⟦ T ⟧ₛ [ T' ]ₛ

    ρ⇒σ : Ren Δ₁ Δ₂ → Sub Δ₁ Δ₂
    subₛ (ρ⇒σ ρ) = `_ ∘ renᵣ ρ

    _≫ᵣᵣ_ : Ren Δ₁ Δ₂ → Ren Δ₂ Δ₃ → Ren Δ₁ Δ₃
    renᵣ (ρ₁ ≫ᵣᵣ ρ₂) = renᵣ ρ₂ ∘ renᵣ ρ₁

    _≫ᵣₛ_ : Ren Δ₁ Δ₂ → Sub Δ₂ Δ₃ → Sub Δ₁ Δ₃
    subₛ (ρ ≫ᵣₛ σ) = subₛ σ ∘ renᵣ ρ

    _≫ₛᵣ_ : Sub Δ₁ Δ₂ → Ren Δ₂ Δ₃ → Sub Δ₁ Δ₃
    subₛ (σ ≫ₛᵣ ρ) = ⟦_⟧ᵣ ρ ∘ subₛ σ

    _≫ₛₛ_ : Sub Δ₁ Δ₂ → Sub Δ₂ Δ₃ → Sub Δ₁ Δ₃
    subₛ (σ₁ ≫ₛₛ σ₂) = ⟦_⟧ₛ σ₂ ∘ subₛ σ₁

  module Denotational where
    open Syntax
    open Syntax.Environment
    open Substitution
    open import Level using (Setω)
    
    record EnvironmentInterface : Setω where
      field 
        ⟦_⟧η   : (Δ : Env) → Set (suc⨆Δ Δ)
        []η    : ⟦ [] ⟧η
        _∷η_   : ∀ {ℓ} {Δ : Env} → Set ℓ → ⟦ Δ ⟧η → ⟦ ℓ ∷ Δ ⟧η
        lookup : ∀ {ℓ} {Δ : Env} → ⟦ Δ ⟧η → ℓ ∈ Δ → Set ℓ 
        lookup-∷η-cancel : ∀ {ℓ} {Δ₁ : Env} {Δ₂ : Env} (A : Set ℓ) (η : ⟦ Δ₂ ⟧η) (ρ : Ren (ℓ′ ∷ Δ₁) Δ₂) → 
          lookup (A ∷η η) (there (renᵣ ρ (here refl))) ≡ lookup η (renᵣ ρ (here refl))

    module Semantics (environment : EnvironmentInterface) where
      open EnvironmentInterface environment
      
      ⟦_⟧T_ : ∀ {ℓ} {Δ : Env} → (T : Type Δ ℓ) → ⟦ Δ ⟧η → Set ℓ
      ⟦ Nat     ⟧T η = ℕ
      ⟦ ` α     ⟧T η = lookup η α
      ⟦ T₁ ⇒ T₂ ⟧T η = ⟦ T₁ ⟧T η → ⟦ T₂ ⟧T η   
      ⟦ ∀α T    ⟧T η = ∀ A → ⟦ T ⟧T (A ∷η η)  

      module Properties where
        open Substitution
        open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

        ⟦_⟧ρ_ : Ren Δ₁ Δ₂ → ⟦ Δ₂ ⟧η → ⟦ Δ₁ ⟧η
        ⟦_⟧ρ_ {Δ₁ = []}    ρ η = []η
        ⟦_⟧ρ_ {Δ₁ = _ ∷ _} ρ η = (⟦ ` renᵣ ρ (here refl) ⟧T η) ∷η (⟦ dropᵣ ρ ⟧ρ η)

        ⟦⟧η-preserves-idᵣ : (ρ : Ren Δ₁ Δ₂) (η : ⟦ Δ₂ ⟧η)  (A : Set ℓ) → (⟦ ρ ≫ᵣᵣ idᵣ ⟧ρ η) ≡ ⟦ ρ ⟧ρ η
        ⟦⟧η-preserves-idᵣ ρ η A = refl

        ⟦⟧η-preserves-skipᵣ : (ρ : Ren Δ₁ Δ₂) (η : ⟦ Δ₂ ⟧η)  (A : Set ℓ) → (⟦ ρ ≫ᵣᵣ skipᵣ ⟧ρ (A ∷η η)) ≡ ⟦ ρ ⟧ρ η
        ⟦⟧η-preserves-skipᵣ {[]} ρ η A    = refl
        ⟦⟧η-preserves-skipᵣ {ℓ ∷ Δ} ρ η A = cong₂ _∷η_ (lookup-∷η-cancel A η ρ) (⟦⟧η-preserves-skipᵣ (dropᵣ ρ) η A)


    module FunctionEnvironment where
      open import BoundQuantification
  
      ℓ∈Δ⇒ℓ<⨆Δ : ∀ {ℓ} {Δ : Env} → ℓ ∈ Δ → ℓ < (suc⨆Δ Δ)
      ℓ∈Δ⇒ℓ<⨆Δ {Δ = ℓ ∷ Δ}  (here refl) = <₃ {ℓ₂ = suc⨆Δ Δ} <₁
      ℓ∈Δ⇒ℓ<⨆Δ {Δ = ℓ′ ∷ Δ} (there x)   = <₃ {ℓ₂ = suc⨆Δ (ℓ′ ∷ Δ)} (ℓ∈Δ⇒ℓ<⨆Δ x)
  
      ⟦_⟧η : (Δ : Env) → Set (suc⨆Δ Δ)
      ⟦ Δ ⟧η = ∀ (l : BoundLevel (suc⨆Δ Δ)) → # l ∈ Δ → BoundLift (#<Λ l) (Set (# l))
  
      []η : ⟦ [] ⟧η
      []η _ ()
  
      _∷η_ : ∀ {ℓ} {Δ : Env} → Set ℓ → ⟦ Δ ⟧η → ⟦ ℓ ∷ Δ ⟧η
      (A ∷η η) l (here refl) = bound-lift (#<Λ l) A
      (A ∷η η) l (there x)   = bound-lift (#<Λ l) (bound-unlift (ℓ∈Δ⇒ℓ<⨆Δ x) (η _ x)) 
  
      lookup : ∀ {ℓ} {Δ : Env} → ⟦ Δ ⟧η → ℓ ∈ Δ → Set ℓ 
      lookup η α = bound-unlift (ℓ∈Δ⇒ℓ<⨆Δ α) (η _ α)

      open Properties using (inverse-property)
      FunctionEnvironment : EnvironmentInterface
      FunctionEnvironment = record 
        { ⟦_⟧η   = ⟦_⟧η 
        ; []η    = []η 
        ; _∷η_   = _∷η_ 
        ; lookup = lookup 
        ; lookup-∷η-cancel = λ A η ρ → inverse-property (ℓ∈Δ⇒ℓ<⨆Δ (renᵣ ρ (here refl))) _
        }
        
    module DatatypeEnvironment where
      open import Data.Unit using (⊤; tt)
      open import Data.Product using (_×_; _,_)
  
      ⟦_⟧η : (Δ : Env) → Set (suc⨆Δ Δ)
      ⟦  []   ⟧η = ⊤
      ⟦ ℓ ∷ Δ ⟧η = Set ℓ × ⟦ Δ ⟧η
  
      []η : ⟦ [] ⟧η
      []η = _
  
      _∷η_ : ∀ {ℓ} {Δ : Env} → Set ℓ → ⟦ Δ ⟧η → ⟦ ℓ ∷ Δ ⟧η
      _∷η_ = _,_
  
      lookup : ∀ {ℓ} {Δ : Env} → ⟦ Δ ⟧η → ℓ ∈ Δ → Set ℓ 
      lookup (A , _) (here refl) = A
      lookup (_ , η) (there α)   = lookup η α
        
      DatatypeEnvironment : EnvironmentInterface
      DatatypeEnvironment = record 
        { ⟦_⟧η   = ⟦_⟧η 
        ; []η    = []η 
        ; _∷η_   = _∷η_ 
        ; lookup = lookup 
        ; lookup-∷η-cancel = λ A η ρ → refl
        }

module Expressions where

  module Syntax where
    open Types
    open Types.Syntax 
    open Types.Syntax.Environment
    open Types.Substitution

    module Context where
      data Ctx (Δ : Env) : Set where
        []   : Ctx Δ
        _∷_  : Type Δ ℓ → Ctx Δ → Ctx Δ

      variable
        Γ Γ′ Γ₁ Γ₂ Γ₃ : Ctx Δ

      data _∋_ : Ctx Δ → Type Δ ℓ → Set where
        here   : (T ∷ Γ) ∋ T
        there  : Γ ∋ T → (T′ ∷ Γ) ∋ T

      ⨆Γ : Ctx Δ → Level
      ⨆Γ []      = zero 
      ⨆Γ (_∷_ {ℓ} T Γ) = ℓ ⊔ ⨆Γ Γ 
      
      Γ₀ : Ctx []
      Γ₀ = []
      -- 
      -- -- functorial action of renamings on environments
      -- 
      renΓ : (ρ : Ren Δ₁ Δ₂) → Ctx Δ₁ → Ctx Δ₂
      renΓ ρ []      = []
      renΓ ρ (T ∷ Γ) = ren ρ T ∷ renΓ ρ Γ
      -- 
      -- ⟦_⟧EEᵣ_ : Env Δ₁ → TRen Δ₁ Δ₂ → Env Δ₂
      -- ⟦_⟧EEᵣ_ = flip ΓRen
      -- 
      -- ⟦_⟧Γidᵣ≗id : (Γ : Env Δ) → ⟦ Γ ⟧EEᵣ Tidᵣ ≡ Γ
      -- ⟦ []    ⟧Γidᵣ≗id = refl
      -- ⟦ T ∷ Γ ⟧Γidᵣ≗id = cong₂ _∷_ ⟦ T ⟧Tidᵣ≗id ⟦ Γ ⟧Γidᵣ≗id
      -- 
      skipᵣΓ : Ctx Δ → Ctx (ℓ ∷ Δ)
      skipᵣΓ = renΓ skipᵣ
      
      syntax skipᵣΓ {ℓ = ℓ} Γ = [ ℓ ]∷ Γ
      -- 
      -- [_] : ∀ l → Env (l ∷ [])
      -- [ l ] = [ l ]∷ []
      -- 
      -- variable Γ Γ₁ Γ₂ Γ₂₁ Γ₂₂ : Env Δ
      -- 
      -- --! inn
      -- data _∈_ : Type Δ l → Env Δ → Set where
      --   here   : T ∈ (T ∷ Γ)
      --   there  : T ∈ Γ → T ∈ (T′ ∷ Γ)
      -- 
      -- -- properties of ⟦_⟧EEᵣ_ wrt _∈_
      -- 
      -- module _ {Δ₁ Δ₂} (ρ : TRen Δ₁ Δ₂) where
      -- 
      --   ΓRen-∈ : T ∈ Γ → (⟦ T ⟧Tᵣ ρ) ∈ (⟦ Γ ⟧EEᵣ ρ)
      --   ΓRen-∈ here      = here
      --   ΓRen-∈ (there x) = there (ΓRen-∈ x)
      -- 
      --   ΓRen-∈⁻¹ : T′ ∈ (⟦ Γ ⟧EEᵣ ρ) → ∃[ T ] T′ ≡ ⟦ T ⟧Tᵣ ρ × T ∈ Γ
      --   ΓRen-∈⁻¹ {Γ = T ∷ _} here      = T , refl , here
      --   ΓRen-∈⁻¹ {Γ = _ ∷ _} (there y) = let T , eq , x = ΓRen-∈⁻¹ y in T , eq , there x
      -- 
      --   ΓRen-∈⁻¹∘ΓRen-∈≗id : (T∈Γ : T ∈ Γ) → ΓRen-∈⁻¹ (ΓRen-∈ T∈Γ) ≡ (_ , refl , T∈Γ)
      --   ΓRen-∈⁻¹∘ΓRen-∈≗id here = refl
      --   ΓRen-∈⁻¹∘ΓRen-∈≗id (there x) = cong (map₂ (map₂ there)) (ΓRen-∈⁻¹∘ΓRen-∈≗id x)
      -- {-
      --   ΓRen-∈∘ΓRen-∈⁻¹≗id : (T∈⟦Γ⟧ρ : T′ ∈ (⟦ Γ ⟧EEᵣ ρ)) →
      --                        let T , eq , T∈Γ = ΓRen-∈⁻¹ T∈⟦Γ⟧ρ in
      --                        subst (_∈ (⟦ Γ ⟧EEᵣ ρ)) eq T∈⟦Γ⟧ρ ≡ ΓRen-∈ T∈Γ
      --   ΓRen-∈∘ΓRen-∈⁻¹≗id {Γ = T ∷ _} here      = refl
      --   ΓRen-∈∘ΓRen-∈⁻¹≗id {Γ = _ ∷ _} (there y)
      --     -- with T , eq , x ← ΓRen-∈⁻¹ y
      --     {- rewrite eq -} = dcong there (ΓRen-∈∘ΓRen-∈⁻¹≗id y)
      -- -}
      -- 
      --   Γliftᵣ : ∀ l Γ → ΓRen (Tliftᵣ ρ) ([ l ]∷ Γ) ≡ ([ l ]∷ ⟦ Γ ⟧EEᵣ ρ)
      --   Γliftᵣ l []      = refl
      --   Γliftᵣ l (T ∷ Γ) = cong₂ _∷_ (swap-Tren-Twk ρ T) (Γliftᵣ l Γ)
      -- 
      -- ⟦_⟧∈-wk : T ∈ Γ → Twk T ∈ ([ l ]∷ Γ)
      -- ⟦_⟧∈-wk = ΓRen-∈ Tskipᵣ
      -- 
      -- ⟦_⟧∈-wk⁻¹ : T′ ∈ ([ l ]∷ Γ) → ∃[ T ] T′ ≡ Twk T × T ∈ Γ
      -- ⟦_⟧∈-wk⁻¹ = ΓRen-∈⁻¹ Tskipᵣ
      -- 
      -- -- functorial action of substitutions on environments
      -- 
      -- ΓSub : (σ : TSub Δ₁ Δ₂) → Env Δ₁ → Env Δ₂
      -- ΓSub σ []      = []
      -- ΓSub σ (T ∷ Γ) = Tsub σ T ∷ ΓSub σ Γ
      -- 
      -- ⟦_⟧EEₛ_ : Env Δ₁ → TSub Δ₁ Δ₂ → Env Δ₂
      -- ⟦_⟧EEₛ_ = flip ΓSub
      -- 
      -- --! DefEidS
      -- ⟦_⟧Γidₛ≗id : (Γ : Env Δ) → ⟦ Γ ⟧EEₛ Tidₛ ≡ Γ
      -- ⟦ []    ⟧Γidₛ≗id = refl
      -- ⟦ T ∷ Γ ⟧Γidₛ≗id = cong₂ _∷_ ⟦ T ⟧Tidₛ≗id ⟦ Γ ⟧Γidₛ≗id
      -- 
      -- module _ {Δ₁ Δ₂} (σ : TSub Δ₁ Δ₂) where
      -- 
      --   ΓSub-∈ : T ∈ Γ → (⟦ T ⟧Tₛ σ) ∈ (⟦ Γ ⟧EEₛ σ)
      --   ΓSub-∈ here      = here
      --   ΓSub-∈ (there x) = there (ΓSub-∈ x)
      -- 
      --   ΓSub-∈⁻¹ : T′ ∈ (⟦ Γ ⟧EEₛ σ) → ∃[ T ] T′ ≡ ⟦ T ⟧Tₛ σ × T ∈ Γ
      --   ΓSub-∈⁻¹ {Γ = _ ∷ _} here      = _ , refl , here
      --   ΓSub-∈⁻¹ {Γ = _ ∷ _} (there y) = let _ , eq , x = ΓSub-∈⁻¹ y in _ , eq , there x
      -- 
      --   ΓSub-∈-id : (T∈Γ : T ∈ Γ) → ΓSub-∈⁻¹ (ΓSub-∈ T∈Γ) ≡ (_ , refl , T∈Γ)
      --   ΓSub-∈-id here      = refl
      --   ΓSub-∈-id (there x) = cong (map₂ (map₂ there)) (ΓSub-∈-id x)
      -- 
      --   Γliftₛ : ∀ l Γ → ⟦ [ l ]∷ Γ ⟧EEₛ Tliftₛ σ ≡ [ l ]∷ ⟦ Γ ⟧EEₛ σ
      --   Γliftₛ l []      = refl
      --   Γliftₛ l (T ∷ Γ) = cong₂ _∷_ (swap-Tsub-Twk σ T) (Γliftₛ l Γ)
      -- 
      -- lemmaΓ : (T : Type Δ l) (Γ : Env Δ) → ΓSub ([ T ]T) ([ l ]∷ Γ) ≡ Γ
      -- lemmaΓ T []       = refl
      -- lemmaΓ T (T′ ∷ Γ) = cong₂ _∷_ (lemmaT T T′) (lemmaΓ T Γ)
      -- 
      -- -- semantic environments
      -- 
      -- -- MW: we switch from our functional environment to again heterogenous lists 
      -- -- so we do not need to live in Setω
      -- VEnv ⟦_⟧EE_ : (Γ : Env Δ) (η : ⟦ Δ ⟧TE) → Set (Γ-level Γ)
      -- ⟦ []    ⟧EE η = ⊤
      -- ⟦ T ∷ Γ ⟧EE η = ⟦ T ⟧T η × ⟦ Γ ⟧EE η
      -- 
      -- VEnv {Δ} Γ η = ⟦ Γ ⟧EE η
      -- 
      -- γ₀ : ⟦ Γ₀ ⟧EE η₀
      -- γ₀ = _
      -- 
      -- variable
      --   γ γ₁ γ₂ : VEnv {Δ} Γ η
      -- 
      -- extend-val : {η : ⟦ Δ ⟧TE} {Γ : Env Δ} {T : Type Δ l} →
      --              ⟦ T ⟧T η → ⟦ Γ ⟧EE η → ⟦ T ∷ Γ ⟧EE η
      -- extend-val v γ = v , γ
      -- 
      -- syntax extend-val {T = T} v γ = v ∷⟦ T ⟧ γ
      -- 
      -- -- MW: since we do not have tskip we need to map a weakening over Γ
      -- -- when consing a semtantic type to η
      -- -- similar to our extend-tskip method we the need transfer lemma 
      -- -- that we can either extend the context or weaken the type
      -- extend-typ :  (⟦α⟧ : Set l) → VEnv {Δ} Γ η → ⟦ [ l ]∷ Γ ⟧EE (⟦α⟧ ∷η η)
      -- extend-typ {Γ = []}    {η = _} _   _           = _
      -- extend-typ {Γ = T ∷ _} {η = η} ⟦α⟧ (v∈⟦T⟧ , γ)
      --   rewrite sym (⟦Twk_⟧T_ T ⟦α⟧ {η = η})
      --   = v∈⟦T⟧ ∷⟦ Twk T ⟧ extend-typ ⟦α⟧ γ
      -- 
      -- syntax extend-typ {l = l} T γ = T ∷[ l ] γ
      

    open Context
  
    data Val {Δ} (Γ : Ctx Δ) : Type Δ ℓ → Set
    data Exp {Δ} (Γ : Ctx Δ) : Type Δ ℓ → Set
    
    data Val {Δ} Γ where
      `_    : Γ ∋ T → Val Γ T
      #_    : ℕ → Val Γ Nat
      λx_   : Exp (T ∷ Γ) T′ → Val Γ (T ⇒ T′)
      Λ_⇒_  : ∀ ℓ {T : Type (ℓ ∷ Δ) ℓ′} → Exp ([ ℓ ]∷ Γ) T → Val Γ (∀α T)
  
    pattern λx∶_⇒_ T e    = λx_ {T = T} e
    pattern Λ_∈_⇒_ T l e = Λ_⇒_ l {T = T} e
  
    data Exp {Δ} Γ where
      val : (v : Val Γ T) → Exp Γ T
      ‵suc : Exp Γ Nat → Exp Γ Nat
      _·_  : (f : Exp Γ (T ⇒ T′)) → Exp Γ T → Exp Γ T′
      _∙_  : Exp Γ (∀α T) → (T′ : Type Δ ℓ) → Exp Γ (T [ T′ ]) 

    