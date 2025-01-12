{-# OPTIONS --rewriting #-}
module BoundedLevelQuantification2 where

import ExtendedLevels as Level
open Level hiding (_<_; Lift; lift)

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Level
  Λ Λ′ Λ₁ Λ₂ Λ₃ : Level

module Ordering where
  data _<_ : Level → Level → Set where
    <₁ : ℓ < suc ℓ
    <₂ : ℓ₁ < ℓ₂ → ℓ₁ < suc ℓ₂
    <₃ : ℓ < ℓ₁ → ℓ < (ℓ₁ ⊔ ℓ₂)

open Ordering public

record Level[_] (Λ : Level) : Set Λ where
  constructor _,_  
  field 
    level : Level
    ℓ<Λ : level < Λ

open Level[_] public

bound : Level[ Λ ] → Level
bound {Λ} _ = Λ

private variable
  l l′ l₁ l₂ : Level[ Λ ] 

Lift  : ∀ (l : Level[ Λ ]) → Set (suc (level l)) → Set Λ
Lift (ℓ , <₁)                          A = Level.Lift (suc ℓ) A
Lift (ℓ , <₂ {ℓ₂ = ℓ₂} ℓ<Λ)            A = Level.Lift {a = ℓ₂} _ (Lift (ℓ , ℓ<Λ) A)
Lift (ℓ , <₃ {ℓ₁ = ℓ₁} {ℓ₂ = ℓ₂}  ℓ<Λ) A = Level.Lift {a = ℓ₁} ℓ₂ (Lift (ℓ , ℓ<Λ) A)

lift : ∀ (l : Level[ Λ ]) → Set (level l) → Lift l (Set (level l))
lift (level , <₁)     A = Level.lift A
lift (level , <₂ ℓ<Λ) A = Level.lift (lift (level , ℓ<Λ) A)
lift (level , <₃ ℓ<Λ) A = Level.lift (lift (level , ℓ<Λ) A)

unlift : ∀ (l : Level[ Λ ]) → Lift l (Set (level l)) → Set (level l)
unlift (level , <₁)     (Level.lift A) = A
unlift (level , <₂ ℓ<Λ) (Level.lift A) = unlift ((level , ℓ<Λ)) A
unlift (level , <₃ ℓ<Λ) (Level.lift A) = unlift ((level , ℓ<Λ)) A

module Properties where
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  inverse-property : ∀ (l : Level[ Λ ]) (A : Set (level l)) → unlift l (lift l A) ≡ A 
  inverse-property (ℓ , <₁)     A = refl
  inverse-property (ℓ , <₂ ℓ<Λ) A = inverse-property (ℓ , ℓ<Λ) A
  inverse-property (ℓ , <₃ ℓ<Λ) A = inverse-property (ℓ , ℓ<Λ) A

module StratifiedSystemFExample where
  open import Data.Nat using (ℕ)
  open import Data.List using (List; []; _∷_)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Data.List.Relation.Unary.All using (All; [] ; _∷_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
  open import Function using (_∘_; id; flip; _$_)

  module Types where
    module Syntax where
      Env = List Level
       
      ⨆_ : Env → Level
      ⨆ []       = zero
      ⨆ (ℓ ∷ ℓs) = suc ℓ ⊔ ⨆ ℓs
      
      data Type (Δ : Env) : Level → Set ω where
        Nat : Type Δ zero
        `_  : ∀ {ℓ} → ℓ ∈ Δ → Type Δ ℓ
        _⇒_ : ∀ {ℓ₁ ℓ₂} → Type Δ ℓ₁ → Type Δ ℓ₂ → Type Δ (ℓ₁ ⊔ ℓ₂)
        ∀α  : ∀ {ℓ ℓ′} → Type (ℓ ∷ Δ) ℓ′ → Type Δ (suc ℓ ⊔ ℓ′)
        Ty  : (l : Level[ ω ]) → Type Δ (suc (level l))
        Tyω : Type Δ ω+1
        
      pattern ∀α:_⇒_ ℓ {ℓ′ = ℓ′} T = ∀α {ℓ = ℓ} {ℓ′ = ℓ′} T

    module Substitution where
      open Syntax   

      private variable
        Δ Δ′ Δ₁ Δ₂ Δ₃ : Env
      
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
          ren : REN Δ₁ Δ₂

        TR-level : Level
        TR-level = (⨆ Δ₁) ⊔ (⨆ Δ₂)

        wkᵣ : REN Δ₁ (ℓ ∷ Δ₂)
        wkᵣ = there ∘ ren

        liftᵣ : REN (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)
        liftᵣ (here refl) = (here refl)
        liftᵣ (there α)   = there $ ren α

      open Ren public using (ren)

      module _ (ρ : Ren Δ₁ Δ₂) where
        wkᵣ : Ren Δ₁ (ℓ ∷ Δ₂)
        ren wkᵣ = Ren.wkᵣ ρ

        liftᵣ : Ren (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)
        ren liftᵣ = Ren.liftᵣ ρ


      private variable
        ρ ρ′ ρ₁ ρ₂ ρ₃ : Ren Δ₁ Δ₂

      idᵣ : Ren Δ Δ
      ren idᵣ = id

      skipᵣ : Ren Δ (ℓ ∷ Δ)
      ren skipᵣ = there

      dropᵣ : Ren (ℓ ∷ Δ₁) Δ₂ → Ren Δ₁ Δ₂
      ren (dropᵣ ρ*) = popᵣ $ ren ρ*

      renᵣ : Ren Δ₁ Δ₂ → Type Δ₁ ℓ → Type Δ₂ ℓ
      renᵣ ρ (` α)     = ` ren ρ α
      renᵣ ρ (T₁ ⇒ T₂) = renᵣ ρ T₁ ⇒ renᵣ ρ T₂
      renᵣ ρ (∀α T)    = ∀α (renᵣ (liftᵣ ρ) T)
      renᵣ ρ Nat       = Nat
      renᵣ ρ (Ty l)    = Ty l
      renᵣ ρ Tyω       = Tyω

      ⟦_⟧ᵣ_ : Type Δ₁ ℓ → Ren Δ₁ Δ₂ → Type Δ₂ ℓ
      ⟦_⟧ᵣ_ = flip renᵣ

      wk : Type Δ ℓ′ → Type (ℓ ∷ Δ) ℓ′
      wk = renᵣ skipᵣ

      SUB : (Δ₁ Δ₂ : Env) → Set ω
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

      record Sub (Δ₁ Δ₂ : Env) : Set ω where
        constructor mkSub
        field
          sub : SUB Δ₁ Δ₂

        TS-level : Level
        TS-level = (⨆ Δ₁) ⊔ (⨆ Δ₂)

        wkₛ : SUB Δ₁ (ℓ ∷ Δ₂)
        wkₛ = wk ∘ sub

        liftₛ : SUB (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)
        liftₛ (here refl)      = ` (here refl)
        liftₛ (there α) = wk $ sub α

        extₛ : Type Δ₂ ℓ → SUB (ℓ ∷ Δ₁) Δ₂
        extₛ T (here refl) = T
        extₛ T (there α)   = sub α


      open Sub public using (sub)

      module _ (σ : Sub Δ₁ Δ₂) where
        wkₛ : Sub Δ₁ (ℓ ∷ Δ₂)
        sub wkₛ = Sub.wkₛ σ

        liftₛ : Sub (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)
        sub liftₛ = Sub.liftₛ σ

        extₛ : Type Δ₂ ℓ → Sub (ℓ ∷ Δ₁) Δ₂
        sub (extₛ T) = Sub.extₛ σ T


      private variable
        σ σ′ σ₁ σ₂ σ₃ : Sub Δ₁ Δ₂

      idₛ : Sub Δ Δ

      sub idₛ = `_

      subₛ : Sub Δ₁ Δ₂ → Type Δ₁ ℓ → Type Δ₂ ℓ
      subₛ σ (` α)     = sub σ α
      subₛ σ (T₁ ⇒ T₂) = subₛ σ T₁ ⇒ subₛ σ T₂
      subₛ σ (∀α T)    = ∀α (subₛ (liftₛ σ) T)
      subₛ σ Nat       = Nat
      subₛ ρ (Ty l)    = Ty l
      subₛ ρ Tyω       = Tyω

      ⟦_⟧ₛ_ : Type Δ₁ ℓ → Sub Δ₁ Δ₂ → Type Δ₂ ℓ
      ⟦_⟧ₛ_ = flip subₛ

      _∷ₛ_ : Type Δ₂ ℓ → Sub Δ₁ Δ₂ → Sub (ℓ ∷ Δ₁) Δ₂
      T ∷ₛ σ = extₛ σ T

      [_] : Type Δ ℓ → Sub (ℓ ∷ Δ) Δ
      [ T ] = T ∷ₛ idₛ

      _[_]ₛ : Type (ℓ ∷ Δ) ℓ′ → Type Δ ℓ → Type Δ ℓ′
      _[_]ₛ T T' = ⟦ T ⟧ₛ [ T' ]

      ρ⇒σ : Ren Δ₁ Δ₂ → Sub Δ₁ Δ₂
      sub (ρ⇒σ ρ) = `_ ∘ ren ρ

      _≫ᵣᵣ_ : Ren Δ₁ Δ₂ → Ren Δ₂ Δ₃ → Ren Δ₁ Δ₃
      ren (ρ₁ ≫ᵣᵣ ρ₂) = ren ρ₂ ∘ ren ρ₁

      _≫ᵣₛ_ : Ren Δ₁ Δ₂ → Sub Δ₂ Δ₃ → Sub Δ₁ Δ₃
      sub (ρ ≫ᵣₛ σ) = sub σ ∘ ren ρ

      _≫ₛᵣ_ : Sub Δ₁ Δ₂ → Ren Δ₂ Δ₃ → Sub Δ₁ Δ₃
      sub (σ ≫ₛᵣ ρ) = ⟦_⟧ᵣ ρ ∘ sub σ

      _≫ₛₛ_ : Sub Δ₁ Δ₂ → Sub Δ₂ Δ₃ → Sub Δ₁ Δ₃
      sub (σ₁ ≫ₛₛ σ₂) = ⟦_⟧ₛ σ₂ ∘ sub σ₁

    module Denotational where
      open Syntax
      
      record Environment : Setε₀ where
        field 
          ⟦_⟧η   : (Δ : Env) → Set (⨆ Δ)
          []η    : ⟦ [] ⟧η
          _∷η_   : ∀ {ℓ} {Δ : Env} → Set ℓ → ⟦ Δ ⟧η → ⟦ ℓ ∷ Δ ⟧η
          lookup : ∀ {ℓ} {Δ : Env} → ⟦ Δ ⟧η → ℓ ∈ Δ → Set ℓ 

      module Semantics (environment : Environment) where
        open Environment environment
        
        ⟦_⟧_ : ∀ {ℓ} {Δ : Env} → (T : Type Δ ℓ) → ⟦ Δ ⟧η → Set ℓ
        ⟦ Nat      ⟧ η = ℕ
        ⟦ ` α      ⟧ η = lookup η α
        ⟦ T₁ ⇒ T₂  ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η   
        ⟦ ∀α T     ⟧ η = ∀ A → ⟦ T ⟧ (A ∷η η)  
        ⟦ Ty l     ⟧ η = Set (level l)
        -- the cast would normally be performed by the compiler
        ⟦ Tyω    ⟧ η = cast β-suc-* (Set ω)
          where β-suc-* = (trans (β-suc-ω {ℓ₁ = one} {ℓ₂ = zero}) (cong (ω↑ one +_) β-suc-zero))
      
      module EnvironmentProperties (environment : Environment) where
        open Substitution
        open Environment environment
        open Semantics environment

        private variable
          Δ Δ′ Δ₁ Δ₂ Δ₃ : Env

        ⟦_⟧ηᵣ_ : ⟦ Δ₂ ⟧η → Ren Δ₁ Δ₂ → ⟦ Δ₁ ⟧η
        ⟦_⟧ηᵣ_ {Δ₁ = []}     η ρ = []η
        ⟦_⟧ηᵣ_ {Δ₁ = ℓ ∷ Δ₁} η ρ = (⟦ ` (ren ρ) (here refl) ⟧ η) ∷η (⟦ η ⟧ηᵣ dropᵣ ρ)

        -- TODO: continue to check that all our desired properties are actually independent of the environment representation 

      module FunctionEnvironment where
        open Level[_]
      
        ℓ∈Δ⇒ℓ<⨆Δ : ∀ {ℓ} {Δ : Env} → ℓ ∈ Δ → ℓ < (⨆ Δ)
        ℓ∈Δ⇒ℓ<⨆Δ {Δ = ℓ ∷ Δ}  (here refl) = <₃ {ℓ₂ = ⨆ Δ} <₁
        ℓ∈Δ⇒ℓ<⨆Δ {Δ = ℓ′ ∷ Δ} (there x)   = <₃ {ℓ₂ = ⨆ (ℓ′ ∷ Δ)} (ℓ∈Δ⇒ℓ<⨆Δ x)
      
        ⟦_⟧η : (Δ : Env) → Set (⨆ Δ)
        ⟦ Δ ⟧η = ∀ (l : Level[ ⨆ Δ ]) → level l ∈ Δ → Lift l (Set (level l)) 
      
        []η : ⟦ [] ⟧η
        []η _ ()
      
        _∷η_ : ∀ {ℓ} {Δ : Env} → Set ℓ → ⟦ Δ ⟧η → ⟦ ℓ ∷ Δ ⟧η
        (A ∷η η) l (here refl) = lift l A
        (A ∷η η) l (there x)   = lift l (unlift  (_ , (ℓ∈Δ⇒ℓ<⨆Δ x)) (η _ x)) 
      
        lookup : ∀ {ℓ} {Δ : Env} → ⟦ Δ ⟧η → ℓ ∈ Δ → Set ℓ 
        lookup η α = unlift (_ , (ℓ∈Δ⇒ℓ<⨆Δ α)) (η _ α)
      
        FunctionEnvironment : Environment
        FunctionEnvironment = record 
          { ⟦_⟧η   = ⟦_⟧η 
          ; []η    = []η 
          ; _∷η_   = _∷η_ 
          ; lookup = lookup 
          }
        
  
      module DatatypeEnvironment where
        open import Data.Unit using (⊤; tt)
        open import Data.Product using (_×_; _,_)
        
        ⟦_⟧η : (Δ : Env) → Set (⨆ Δ)
        ⟦  []   ⟧η = ⊤
        ⟦ ℓ ∷ Δ ⟧η = Set ℓ × ⟦ Δ ⟧η

        []η : ⟦ [] ⟧η
        []η = _

        _∷η_ : ∀ {ℓ} {Δ : Env} → Set ℓ → ⟦ Δ ⟧η → ⟦ ℓ ∷ Δ ⟧η
        _∷η_ = _,_

        lookup : ∀ {ℓ} {Δ : Env} → ⟦ Δ ⟧η → ℓ ∈ Δ → Set ℓ 
        lookup (A , _) (here refl) = A
        lookup (_ , η) (there α)   = lookup η α
        
        DatatypeEnvironment : Environment
        DatatypeEnvironment = record 
          { ⟦_⟧η   = ⟦_⟧η 
          ; []η    = []η 
          ; _∷η_   = _∷η_ 
          ; lookup = lookup 
          }
        