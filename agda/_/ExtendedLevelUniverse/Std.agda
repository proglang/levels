{-# OPTIONS --rewriting --erased-cubical --no-load-primitives #-}

module Std where

open import Prelude

-- Agda.Builtin.Unit
record ⊤ : Set where
  instance constructor tt

{-# BUILTIN UNIT ⊤ #-}
{-# COMPILE GHC ⊤ = data () (()) #-}

-- Agda.Builtin.Nat
data ℕ : Set where
  zeroₙ : ℕ
  sucₙ  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Agda.Builtin.List
infixr 5 _∷_
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

-- Agda.Builtin.Sigma
record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
  
open Σ public
  
infixr 4 _,_

-- Data.Product.Base

∃ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃ = Σ _

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ
  
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B
  
infix 2 ∃-syntax
  
∃-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃-syntax = ∃
  
syntax ∃-syntax (λ x → B) = ∃[ x ] B

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = Σ[ x ∈ A ] B

-- Relation.Unary 
Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Pred A ℓ = A → Set ℓ

-- Data.List.Relation.Unary.Any
data Any {a p} {A : Set a} (P : Pred A p) : Pred (List A) (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

-- Data.List.Membership.PropositionalEquality
_∈_ : ∀ {a} {A : Set a} → A → List A → Set _
x ∈ xs = Any (x ≡_) xs

-- Data.List.Relation.Unary.All 
data All {a p} {A : Set a} (P : Pred A p) : Pred (List A) (a ⊔ p) where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

-- Function.Base
id : ∀ {a} {A : Set a} → A → A
id x = x

infixr 9 _∘_
_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
    (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
    ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-}

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
     ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y
{-# INLINE flip #-}

_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
    ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
{-# INLINE _$_ #-}