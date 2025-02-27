{-# OPTIONS --warn=noUserWarning #-}
module SSF-IR where

open import Level using (zero)
open import Data.Nat using (ℕ; s≤s; z≤n; _<′_ ) renaming (_⊔_ to _⊔ℕ_; _+_ to _+ℕ_; _<_ to _<ℕ_ )
open import Data.Nat.Properties using (<-trans; <-irrefl; ≡-irrelevant; <-asym)
open import Data.Vec using (Vec)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product.Properties using (×-≡,≡←≡)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning

open import Universe using (module Lib; module IRUniverse)
open Lib

--! IR >

module _ where
  coe-coe : ∀{ℓ}{A B : Set ℓ} (a≡b : A ≡ B) (b≡a : B ≡ A) {a : A} → 
    (coe b≡a (coe a≡b a)) ≡ a
  coe-coe refl refl = refl

open IRUniverse

module _ where
  open ℕ*ℕ hiding (#_) public
  open IR-Universe lvl

  import Data.Nat as N
  open import Data.Nat.Properties
  open import Data.Nat.Induction
  open Lexicographic N._<_ (λ _ → N._<_)

  _<ℕ*ℕ_ : ℕ × ℕ → ℕ × ℕ → Set
  _<ℕ*ℕ_ = Lexicographic._<_ _<ℕ_ (λ _ → _<ℕ_)
  
  <-irrefl-ℕ*ℕ : Irreflexive _≡_ _<ℕ*ℕ_
  <-irrefl-ℕ*ℕ refl (Lexicographic.left x₁<x₂) = <-irrefl refl x₁<x₂
  <-irrefl-ℕ*ℕ refl (Lexicographic.right y₁<y₂) = <-irrefl refl y₁<y₂

  ≡-decompose : ∀ {x y : ℕ × ℕ} → (p : x ≡ y) → 
    Σ (₁ x ≡ ₁ y) (λ p₁ → (Σ (₂ x ≡ ₂ y) (λ p₂ → p ≡ cong₂ _,_ p₁ p₂)))
  ≡-decompose p
    with ×-≡,≡←≡ p
  ≡-decompose refl | refl , refl = refl , refl , refl

  ≡-irrelevant-ℕ*ℕ : Irrelevant {A = ℕ × ℕ} _≡_
  ≡-irrelevant-ℕ*ℕ p₁ p₂
    with ≡-decompose p₁ | ≡-decompose p₂
  ... | p₁-l , p₁-r , dec₁ | p₂-l , p₂-r , dec₂ =
    trans dec₁ (trans (cong₂ (cong₂ _,_) (≡-irrelevant p₁-l p₂-l) (≡-irrelevant p₁-r p₂-r)) (sym dec₂))

  cmp-ℕ : (i j : ℕ) → i <ℕ j ⊎ j <ℕ i ⊎ i ≡ j
  cmp-ℕ ℕ.zero ℕ.zero = inj₂ (inj₂ refl)
  cmp-ℕ ℕ.zero (ℕ.suc j) = inj₁ (s≤s z≤n)
  cmp-ℕ (ℕ.suc i) ℕ.zero = inj₂ (inj₁ (s≤s z≤n))
  cmp-ℕ (ℕ.suc i) (ℕ.suc j)
    with cmp-ℕ i j
  ... | inj₁ x = inj₁ (s≤s x)
  ... | inj₂ (inj₁ x) = inj₂ (inj₁ (s≤s x))
  ... | inj₂ (inj₂ y) = inj₂ (inj₂ (ℕ.suc & y))

  cmp-ℕ*ℕ : (i j : ℕ × ℕ) →
      i <ℕ*ℕ j ⊎ j <ℕ*ℕ i ⊎ i ≡ j
  cmp-ℕ*ℕ i@(ifst , isnd) j@(jfst , jsnd)
    with cmp-ℕ ifst jfst
  ... | inj₁ x = inj₁ (left x)
  ... | inj₂ (inj₁ x) = inj₂ (inj₁ (left x))
  ... | inj₂ (inj₂ refl)
    with cmp-ℕ isnd jsnd
  ... | inj₁ x = inj₁ (right x)
  ... | inj₂ (inj₁ x) = inj₂ (inj₁ (right x))
  ... | inj₂ (inj₂ eq) = inj₂ (inj₂ (cong (λ j → (ifst , j)) eq))

  ≤-suc : ∀ {i j} → ℕ.suc i <ℕ ℕ.suc j → i <ℕ j
  ≤-suc (s≤s p) = p

  <-ext-ℕ : {i j : ℕ}
    → (∀ (k : ℕ) → (k <ℕ i → k <ℕ j) × (k <ℕ j → k <ℕ i))
    → i ≡ j
  <-ext-ℕ {i} {j} f
    with cmp-ℕ i j
  ... | inj₁ x = ⊥-elim (<-irrefl refl (Σ.proj₂ (f i) x))
  ... | inj₂ (inj₁ x) = ⊥-elim (<-irrefl refl (Σ.proj₁ (f j) x))
  ... | inj₂ (inj₂ refl) = refl
  
  <-ext-ℕ*ℕ : ∀ {i j : ℕ × ℕ} →
      ((k : ℕ × ℕ) → (k <ℕ*ℕ i → k <ℕ*ℕ j) × (k <ℕ*ℕ j → k <ℕ*ℕ i)) →
      i ≡ j
  <-ext-ℕ*ℕ {i} {j} f
    with cmp-ℕ*ℕ i j
  ... | inj₁ x = ⊥-elim (<-irrefl-ℕ*ℕ refl (Σ.proj₂ (f i) x))
  ... | inj₂ (inj₁ x) = ⊥-elim (<-irrefl-ℕ*ℕ refl (Σ.proj₁ (f j) x))
  ... | inj₂ (inj₂ refl) = refl

  <-trans-ℕ*ℕ : ∀ {x y z} → x <ℕ*ℕ y → y <ℕ*ℕ z → x <ℕ*ℕ z
  <-trans-ℕ*ℕ (Lexicographic.left x₁<x₂) (Lexicographic.left x₂<x₃) = left (<-trans x₁<x₂ x₂<x₃)
  <-trans-ℕ*ℕ (Lexicographic.left x₁<x₂) (Lexicographic.right y₁<y₂) = left x₁<x₂
  <-trans-ℕ*ℕ (Lexicographic.right y₁<y₂) (Lexicographic.left x₁<x₂) = left x₁<x₂
  <-trans-ℕ*ℕ (Lexicographic.right y₁<y₂) (Lexicographic.right y₂<y₃) = right (<-trans y₁<y₂ y₂<y₃)

  ordinal-ℕ*ℕ : Ordinal lvl
  ordinal-ℕ*ℕ = record { cmp = cmp-ℕ*ℕ ; <-ext = <-ext-ℕ*ℕ }

  sucL : Lvl → Lvl
  sucL (fst , snd) = fst , ℕ.suc snd

open IR-Univ-Ordinal ordinal-ℕ*ℕ renaming (Lvl to ℕ×ℕ)

variable 
  n n′ n₁ n₂ n₃ : ℕ
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : ℕ×ℕ
  
module _ where
  ≤-trans : ∀ {i} {j} {k} → i ≤ j → j ≤ k → i ≤ k
  ≤-trans (inj₁ i<j) (inj₁ j<k) = inj₁ (<-trans-ℕ*ℕ i<j j<k)
  ≤-trans (inj₁ i<j) (inj₂ refl) = inj₁ i<j
  ≤-trans (inj₂ refl) j≤k = j≤k
  
  <≤-trans : ∀ {i} {j} {k} → i <ℕ*ℕ j → j ≤ k → i <ℕ*ℕ k
  <≤-trans i<j (inj₁ j<k) = <-trans-ℕ*ℕ i<j j<k
  <≤-trans i<j (inj₂ refl) = i<j

--!! LEnv
LEnv = List ⊤

variable
  δ δ′ δ₁ δ₂ δ₃ : LEnv

--! Mode
data Mode : Set where
  fin any : Mode 

variable
  μ μ′ μ₁ μ₂ μ₃ : Mode

--! Lvl
data Lvl (δ : LEnv) : Mode → Set where 
  `zero  : Lvl δ fin
  `suc   : Lvl δ μ → Lvl δ μ
  `_     : tt ∈ δ → Lvl δ fin
  _`⊔_   : Lvl δ μ → Lvl δ μ → Lvl δ μ
  ⟨_⟩    : Lvl δ fin → Lvl δ any
  `ω     : Lvl δ any

variable 
  l l′ l₁ l₂ l₃ : Lvl δ any

Lwk  : Lvl δ μ → Lvl (tt ∷ δ) μ
Lwk `zero       = `zero
Lwk (`suc l)    = `suc (Lwk l)
Lwk (` x)       = ` (there x)
Lwk (l₁ `⊔ l₂)  = Lwk l₁ `⊔ Lwk l₂
Lwk ⟨ l ⟩       = ⟨ Lwk l ⟩
Lwk `ω          = `ω

_[_]L : Lvl (tt ∷ δ) μ → Lvl δ fin → Lvl δ μ
`zero          [ l′ ]L  = `zero
`suc l         [ l′ ]L  = `suc (l [ l′ ]L)
(` here refl)  [ l′ ]L  = l′
(` there x)    [ l′ ]L  = ` x
(l₁ `⊔ l₂)     [ l′ ]L  = (l₁ [ l′ ]L) `⊔ (l₂ [ l′ ]L)
⟨ l ⟩          [ l′ ]L  = ⟨ l [ l′ ]L ⟩
`ω             [ l′ ]L  = `ω 

--! LEnvSem
⟦_⟧δ        : LEnv → Set
⟦ []    ⟧δ  = ⊤
⟦ _ ∷ δ ⟧δ  = ℕ × ⟦ δ ⟧δ

variable
  κ κ′ κ₁ κ₂ κ₃ : ⟦ δ ⟧δ

_∷κ_ : ℕ → ⟦ δ ⟧δ → ⟦ tt ∷ δ ⟧δ
_∷κ_ = _,_

lookup-κ : ⟦ δ ⟧δ → tt ∈ δ → ℕ
lookup-κ {_ ∷ δ} (ℓ , κ) (here refl) = ℓ
lookup-κ {_ ∷ δ} (ℓ , κ) (there x)   = lookup-κ κ x

drop-κ : ⟦ tt ∷ δ ⟧δ → ⟦ δ ⟧δ
drop-κ (_ , κ) = κ

--! LSemFin
⟦_⟧L′ : Lvl δ fin → ⟦ δ ⟧δ → ℕ
⟦ `zero     ⟧L′ κ  = ℕ.zero
⟦ `suc l    ⟧L′ κ  = ℕ.suc (⟦ l ⟧L′ κ)
⟦ l₁ `⊔ l₂  ⟧L′ κ  = ⟦ l₁ ⟧L′ κ ⊔ℕ ⟦ l₂ ⟧L′ κ
⟦ ` x       ⟧L′ κ  = lookup-κ κ x

--! LSemAny
⟦_⟧L : Lvl δ any → ⟦ δ ⟧δ → ℕ×ℕ
⟦ ⟨ l ⟩     ⟧L κ  = ℕ.zero , ⟦ l ⟧L′ κ
⟦ `suc l    ⟧L κ  = sucL (⟦ l ⟧L κ)
⟦ l₁ `⊔ l₂  ⟧L κ  = ⟦ l₁ ⟧L κ ⊔ ⟦ l₂ ⟧L κ
⟦ `ω        ⟧L κ  = ω

postulate
  ⟦Lwk⟧L : ∀ (l : Lvl δ any) (κ : ⟦ δ ⟧δ) ℓ → 
    ⟦ Lwk l ⟧L (ℓ ∷κ κ) ≡ ⟦ l ⟧L κ
  ⟦[]L⟧L : ∀ (l : Lvl (tt ∷ δ) any) (κ : ⟦ δ ⟧δ) l′ → 
    ⟦ l [ l′ ]L ⟧L κ ≡ ⟦ l ⟧L (⟦ l′ ⟧L′ κ , κ)

--! TEnv
data TEnv : LEnv → Set where
  []   : TEnv δ
  _∷_  : Lvl δ any → TEnv δ → TEnv δ 
  ∷l_  : TEnv δ → TEnv (tt ∷ δ) 

variable
  Δ Δ′ Δ₁ Δ₂ Δ₃ : TEnv δ

--! TEnvNi
data _∍_ : TEnv δ → Lvl δ any → Set where
  here   : (l ∷ Δ) ∍ l
  there  : Δ ∍ l → (l′ ∷ Δ) ∍ l
  lskip  : Δ ∍ l → (∷l Δ) ∍ Lwk l

--! Type
data Type (Δ : TEnv δ) : Lvl δ any → Set where
  Nat   : Type Δ ⟨ `zero ⟩
  `_    : Δ ∍ l → Type Δ l
  _⇒_   : Type Δ l₁ → Type Δ l₂ → Type Δ (l₁ `⊔ l₂) 
  ∀α    : Type (l ∷ Δ) l′ → Type Δ (`suc l `⊔ l′) 
  ∀ℓ    : Type (∷l Δ) (Lwk l) → Type Δ (`ω `⊔ l)

variable
  T T′ T₁ T₂ T₃ : Type Δ l

postulate
  TTwk    : Type Δ l′ → Type (l ∷ Δ) l′
  TLwk    : Type Δ l → Type (∷l Δ) (Lwk l)
  _[_]TT  : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
  _[_]TL  : Type (∷l Δ) l → (l′ : Lvl δ fin) → Type Δ (l [ l′ ]L)

--! FTSEAsFunction
⟦_⟧Δ : (Δ : TEnv δ) → (κ : ⟦ δ ⟧δ) → Set 
⟦  []    ⟧Δ κ  = ⊤
⟦ l ∷ Δ  ⟧Δ κ  = U (⟦ l ⟧L κ) × ⟦ Δ ⟧Δ κ
⟦ ∷l Δ   ⟧Δ κ  = ⟦ Δ ⟧Δ (drop-κ κ)

_∷η_ : {κ : ⟦ δ ⟧δ} →  U (⟦ l ⟧L κ) → ⟦ Δ ⟧Δ κ → ⟦ l ∷ Δ ⟧Δ κ
_∷η_ = _,_

lookup-η : {κ : ⟦ δ ⟧δ} → ⟦ Δ ⟧Δ κ → Δ ∍ l → U (⟦ l ⟧L κ)
lookup-η (A , _) here                    = A
lookup-η (_ , η) (there x)               = lookup-η η x
lookup-η {κ = ℓ , κ} η (lskip {l = l} x) = coe (cong U (sym (⟦Lwk⟧L l κ ℓ))) (lookup-η η x)

drop-η : {κ : ⟦ δ ⟧δ} → ⟦ l ∷ Δ ⟧Δ κ → ⟦ Δ ⟧Δ κ 
drop-η (_ , η) = η

--! encode
encode : {Δ : TEnv δ} → (T : Type Δ l) → (κ : ⟦ δ ⟧δ) → (η : ⟦ Δ ⟧Δ κ) → U (⟦ l ⟧L κ)
encode Nat       κ η  = ℕ'
encode (` x)     κ η  = lookup-η η x
encode (T₁ ⇒ T₂) κ η  =  Lift≤ (⊔₁ _ _) (encode T₁ κ η) ⇒' Lift≤ (⊔₂ _ _) (encode T₂ κ η)
encode {Δ = Δ} (∀α {l = l} T) κ η =
    let pu = <≤-trans ℕ*ℕ.<suc (⊔₁ _ _) in
    Π' (U' pu) λ A → 
    let eq = Uⁱʳ & ext (λ j → ext (λ p → (λ acc → (U< {⟦ l ⟧L κ} ⦃ acc ⦄ j p)) & (Acc-prop _ wf))) in
    let S = encode T κ (_∷η_ {l = l} {Δ = Δ} {κ = κ} (coe eq A) η) in 
    Lift≤ (⊔₂ _ _) S
encode (∀ℓ {l = l} T) κ η = Π' ℕ' λ ℓ → 
    let S = coe (U & ⟦Lwk⟧L l κ ℓ) (encode T (ℓ ∷κ κ) η) in 
    Lift≤ (⊔₂ ω _) S

-- alternative
-- encode (T₁ ⇒ T₂) κ η  =  Π'' (encode T₁ κ η) (λ _ → encode T₂ κ η)


--! TSem
⟦_⟧T : {Δ : TEnv δ} (T : Type Δ l) (κ : ⟦ δ ⟧δ) (η : ⟦ Δ ⟧Δ κ) → Set
⟦ T ⟧T κ η  = El (encode T κ η)

postulate
  ⟦TLwk⟧T : {Δ : TEnv δ} {T : Type Δ l} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} →
    ⟦ T ⟧T κ η ≡ ⟦ TLwk T ⟧T (n , κ) η 
  ⟦TTwk⟧T : {Δ : TEnv δ} {T : Type Δ l} {κ : ⟦ δ ⟧δ} {A : U (⟦ l′ ⟧L κ)} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ T ⟧T κ η ≡ ⟦ TTwk {l = l′} T ⟧T κ (A , η)
  -- interesting: does not lead to subst hell. in constrast, working with `Set ℓ` for the semantic of types
  -- leads to it (see SSF-EH). there we need to use a cast to write this expression.

  ⟦[]LT⟧T : {Δ : TEnv δ} {T : Type (∷l Δ) (Lwk l)} {l′ : Lvl δ fin} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} →  
    ⟦ T ⟧T (⟦ l′ ⟧L′ κ , κ) η ≡ ⟦ T [ l′ ]TL ⟧T κ η
  ⟦[]TT⟧T : {l′ : Lvl δ any} {T : Type (l′ ∷ Δ) l} {T′ : Type Δ l′} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ T ⟧T κ (_∷η_ {l = l′} {Δ = Δ} {κ = κ} (encode T′ κ η) η) ≡ ⟦ T [ T′ ]TT ⟧T κ η

--! EEnv
data EEnv : (Δ : TEnv δ) → Set where
  []    : EEnv Δ
  _∷_   : Type Δ l → EEnv Δ → EEnv Δ
  _∷l_  : (l : Lvl δ any) → EEnv Δ → EEnv (l ∷ Δ)
  ∷l_   : EEnv Δ → EEnv (∷l Δ)

variable
  Γ Γ′ Γ₁ Γ₂ Γ₃ : EEnv Δ

--! EEnvNi
data _∋_ : EEnv Δ → Type Δ l → Set where
  here   : (T ∷ Γ) ∋ T
  there  : Γ ∋ T → (T′ ∷ Γ) ∋ T
  tskip  : Γ ∋ T → (l ∷l Γ) ∋ TTwk T
  lskip  : Γ ∋ T → (∷l Γ) ∋ TLwk T

--! Expr
data Expr {Δ : TEnv δ} (Γ : EEnv Δ) : Type Δ l → Set where
  Λℓ_   : {T : Type (∷l Δ) (Lwk l)} → Expr (∷l Γ) T → Expr Γ (∀ℓ T)
  _∙ℓ_  : {T : Type (∷l Δ) (Lwk l)} → Expr Γ (∀ℓ T) → (l′ : Lvl δ fin) → Expr Γ (T [ l′ ]TL) 

  `_    : Γ ∋ T → Expr Γ T
  #_    : ℕ → Expr Γ Nat
  ‵suc  : Expr Γ Nat → Expr Γ Nat
  λx_   : Expr (T ∷ Γ) T′ → Expr Γ (T ⇒ T′)
  Λ_⇒_  : (l : Lvl δ any) {T : Type (l ∷ Δ) l′} → Expr (l ∷l Γ) T → Expr Γ (∀α T)
  _·_   : Expr Γ (T₁ ⇒ T₂) → Expr Γ T₁ → Expr Γ T₂
  _∙_   : Expr Γ (∀α T) → (T′ : Type Δ l) → Expr Γ (T [ T′ ]TT) 

module TEnvSemDisplay where
  postulate
--!! TEnvSemDisplay
     ⟦_⟧Γ

          : ℕ → ℕ

--! TEnvSem
⟦_⟧Γ   : {Δ : TEnv δ} → (Γ : EEnv Δ) → (κ : ⟦ δ ⟧δ) → ⟦ Δ ⟧Δ κ → Set
⟦ []     ⟧Γ κ η = ⊤
⟦ T ∷ Γ  ⟧Γ κ η = ⟦ T ⟧T κ η × ⟦ Γ ⟧Γ κ η
⟦_⟧Γ {Δ = l ∷ Δ} (l ∷l Γ) κ η = ⟦ Γ ⟧Γ κ (drop-η {l = l} {Δ = Δ} {κ = κ} η) 
⟦ ∷l Γ   ⟧Γ κ η = ⟦ Γ ⟧Γ (drop-κ κ) η 
   
_∷γ_ : {Δ : TEnv δ} {T : Type Δ l} {Γ : EEnv Δ} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ T ⟧T κ η → ⟦ Γ ⟧Γ κ η → ⟦ T ∷ Γ ⟧Γ κ η
_∷γ_ = _,_

lookup-γ : {Δ : TEnv δ} {Γ : EEnv Δ} {T : Type Δ l} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ Γ ⟧Γ κ η → Γ ∋ T → ⟦ T ⟧T κ η 
lookup-γ (A , γ) here       = A
lookup-γ (_ , γ) (there x)  = lookup-γ γ x
lookup-γ γ (tskip x) = coe ⟦TTwk⟧T (lookup-γ γ x)
lookup-γ γ (lskip x) = coe ⟦TLwk⟧T (lookup-γ γ x)

lemma : ∀ (I : Set) (R : I → I → Set) {i₁ i₂ : I} → 
  i₁ ≡ i₂ → 
  (∀ j → R j i₁ → Set) ≡ (∀ j → R j i₂ → Set)
lemma I R refl = refl

crucial : ∀ {κ : ⟦ δ ⟧δ} (l : Lvl δ any) ℓ (code : U (⟦ Lwk l ⟧L (ℓ ∷κ κ)))  → 
          Elⁱʳ {⟦ l ⟧L κ} {U< {⟦ l ⟧L κ}} (coe (cong U (⟦Lwk⟧L l κ ℓ)) code) ≡ 
          Elⁱʳ {⟦ Lwk l ⟧L (ℓ ∷κ κ)} {U< {⟦ Lwk l ⟧L (ℓ ∷κ κ)}} code
crucial {κ = κ} l ℓ code = generalized _ _ code (⟦Lwk⟧L l κ ℓ)
  where generalized : (ℓ₁ ℓ₂ : ℕ×ℕ) (code : U ℓ₁) (eq : ℓ₁ ≡ ℓ₂) →
                      Elⁱʳ {ℓ₂} {U< {ℓ₂}} (coe (cong U eq) code) ≡ Elⁱʳ {ℓ₁} {U< {ℓ₁}} code
        generalized _ _ _ refl = refl

--! ESem
⟦_⟧E : {Δ : TEnv δ} {T : Type Δ l} {Γ : EEnv Δ} → 
  (e : Expr Γ T) (κ : ⟦ δ ⟧δ) (η : ⟦ Δ ⟧Δ κ) (γ : ⟦ Γ ⟧Γ κ η) → ⟦ T ⟧T κ η
⟦ ` x     ⟧E κ η γ = lookup-γ γ x
⟦ # n     ⟧E κ η γ = n
⟦ ‵suc e  ⟧E κ η γ = ℕ.suc (⟦ e ⟧E κ η γ)
⟦_⟧E {T = (_⇒_ {l₁ = l₁} {l₂ = l₂} T₁ T₂)} {Γ} (λx e) κ η γ = λ x → 
  let eq₁ = ElLift≤ (⊔₁ _ _) (encode T₁ κ η) in
  let γ′ = _∷γ_ {T = T₁} {Γ = Γ} (coe eq₁ x) γ in
  let eq₂ = sym (ElLift≤ (⊔₂ (⟦ l₁ ⟧L κ) _) (encode T₂ κ η)) in 
  coe eq₂ (⟦ e ⟧E κ η γ′)
⟦ _·_ {l₁} {T₁ = T₁} {l₂} {T₂ = T₂} e₁  e₂ ⟧E  κ η γ = 
  let eq₁ = sym (ElLift≤ (⊔₁ _ (⟦ l₂ ⟧L κ)) (encode T₁ κ η)) in
  let eq₂ = ElLift≤ (⊔₂ (⟦ l₁ ⟧L κ) _) (encode T₂ κ η) in
  coe eq₂ (⟦ e₁ ⟧E κ η γ (coe eq₁ (⟦ e₂ ⟧E κ η γ)))
⟦_⟧E {Δ = Δ} {T = ∀α {l′ = l′} T} (Λ l ⇒ e) κ η γ = λ A → 
  let eq = (Uⁱʳ & ext (λ j → ext (λ p → cong (λ acc → (U< {⟦ l ⟧L κ} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) in
  let η′ =  _∷η_ {l = l} {Δ = Δ} {κ = κ} (coe eq A) η in
  let eq = sym (ElLift≤ (⊔₂ (⟦ `suc l ⟧L κ) (⟦ l′ ⟧L κ)) (encode T κ η′)) in 
  coe eq (⟦ e ⟧E κ η′ γ)
⟦_⟧E {Δ = Δ} (_∙_ {l′} {l = l} {T = T} e T′) κ η γ = 
  let eq₁ = Uⁱʳ & ext (λ j → ext (λ p → cong (λ acc → (U< {⟦ l ⟧L κ} ⦃ acc ⦄ j p)) (Acc-prop _ wf))) in
  let eq₂ = Uⁱʳ & (ext (λ j → ext (λ p → trans (U<-compute {⟦ l ⟧L κ} {wf} {j} {p}) (sym U<-compute)))) in
  let eq₃ = cong (λ A → let η′ = _∷η_ {l = l} {Δ = Δ} {κ = κ} A η in 
            Elⁱʳ (Lift≤ (⊔₂ (⟦ `suc l ⟧L κ) _) (encode T κ η′))) (coe-coe eq₂ eq₁) in
  let eq₄ = let η′ = _∷η_ {l = l} {Δ = Δ} {κ = κ} (encode T′ κ η) η in 
            ElLift≤ (⊔₂ (⟦ `suc l ⟧L κ) _) (encode T κ η′) in
  let eq₅ = trans (trans eq₃ eq₄) ⟦[]TT⟧T in
  coe eq₅ (⟦ e ⟧E κ η γ (coe eq₂ (encode T′ κ η)))
⟦_⟧E {T = ∀ℓ {l = l} T} (Λℓ e) κ η γ = λ ℓ → 
  let eq₁ = ElLift≤ (⊔₂ ω (⟦ l ⟧L κ)) (coe (cong U (⟦Lwk⟧L l κ ℓ)) (encode T (ℓ ∷κ κ) η)) in
  let eq₂ = crucial l ℓ (encode T (ℓ ∷κ κ) η) in
  coe (sym (trans eq₁ eq₂)) (⟦ e ⟧E (ℓ ∷κ κ) η γ)
⟦ _∙ℓ_ {l = l} {T = T} e l′ ⟧E κ η γ = 
  let eq₁ = ElLift≤ (⊔₂ ω (⟦ l ⟧L κ)) (coe (U & ⟦Lwk⟧L l κ (⟦ l′ ⟧L′ κ)) (encode T (⟦ l′ ⟧L′ κ ∷κ κ) η)) in
  let eq₂ = trans eq₁ (trans (crucial l (⟦ l′ ⟧L′ κ) (encode T (⟦ l′ ⟧L′ κ ∷κ κ) η)) ⟦[]LT⟧T) in 
  coe eq₂ (⟦ e ⟧E κ η γ (⟦ l′ ⟧L′ κ))
