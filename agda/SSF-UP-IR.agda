module SSF-UP-IR where

open import Level using (zero)
open import Data.Nat using ( ℕ; s≤s; z≤n; _<′_ ) renaming (_⊔_ to _⊔ℕ_; _+_ to _+ℕ_; _<_ to _<ℕ_ )
open import Data.Nat.Properties using (+-identityʳ; +-suc; <-trans; <⇒<′; ⊔-idem; m≤n⇒m⊔n≡n; m≥n⇒m⊔n≡m; <⇒≤; <-irrefl; ≡-irrelevant; <-asym)
open import Data.Vec using (Vec)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup; lookupAny)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product.Properties using (×-≡,≡→≡ ; ×-≡,≡←≡; ×-≡,≡↔≡)
open import Function  using (id; _∘_)
open import Relation.Binary.PropositionalEquality using ()
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Universe using (module Lib; module IRUniverse)
open Lib

coe-coe : ∀{a}{A B : Set a} (x≡y : A ≡ B) (y≡x : B ≡ A) {p : A}
  → (coe y≡x (coe x≡y p)) ≡ p
coe-coe refl refl = refl

open IRUniverse

module _ where
  open ℕ*ℕ-example public
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

  ≡-decompose : ∀ {x y : ℕ × ℕ} → (p : x ≡ y) → Σ (₁ x ≡ ₁ y) (λ p₁ → (Σ (₂ x ≡ ₂ y) (λ p₂ → p ≡ cong₂ _,_ p₁ p₂)))
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

  Lvl-suc : Lvl → Lvl
  Lvl-suc (fst , snd) = fst , ℕ.suc snd

  Lvl-suc-mon : ∀ {x}{y} → x <ℕ*ℕ y → Lvl-suc x <ℕ*ℕ Lvl-suc y
  Lvl-suc-mon (Lexicographic.left x₁<x₂) = Lexicographic.left x₁<x₂
  Lvl-suc-mon (Lexicographic.right y₁<y₂) = Lexicographic.right (s≤s y₁<y₂)

open IR-Univ-Ordinal ordinal-ℕ*ℕ

variable ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Lvl

<-asym-ℕ*ℕ : Asymmetric _<_
<-asym-ℕ*ℕ (Lexicographic.left x₁<x₂) (Lexicographic.left x₂<x₁) = <-asym x₁<x₂ x₂<x₁
<-asym-ℕ*ℕ (Lexicographic.left x₁<x₂) (Lexicographic.right y₁<y₂) = <-irrefl refl x₁<x₂
<-asym-ℕ*ℕ (Lexicographic.right y₁<y₂) (Lexicographic.left x₁<x₂) = <-irrefl refl x₁<x₂ 
<-asym-ℕ*ℕ (Lexicographic.right y₁<y₂) (Lexicographic.right y₂<y₁) = <-asym y₁<y₂ y₂<y₁

≤-antisym : Antisymmetric _≡_ _≤_
≤-antisym (inj₁ x) (inj₁ y) = ⊥-elim (<-asym-ℕ*ℕ x y)
≤-antisym (inj₁ x) (inj₂ refl) = refl
≤-antisym (inj₂ refl) (inj₁ x) = refl
≤-antisym (inj₂ refl) (inj₂ refl) = refl


Lvl-suc-⊔ : ∀ ℓ₁ ℓ₂ → Lvl-suc (ℓ₁ ⊔ ℓ₂) ≡ Lvl-suc ℓ₁ ⊔ Lvl-suc ℓ₂
Lvl-suc-⊔ ℓ₁ ℓ₂
  with cmp ℓ₁ ℓ₂ | cmp (Lvl-suc ℓ₁) (Lvl-suc ℓ₂)
... | inj₁ x | inj₁ x₁ = refl
... | inj₁ x | inj₂ (inj₁ x₁) = ≤-antisym (inj₁ x₁) (inj₁ (Lvl-suc-mon x))
... | inj₁ x | inj₂ (inj₂ refl) = refl
... | inj₂ (inj₁ x₁) | inj₁ x = ⊥-elim (<-asym-ℕ*ℕ x (Lvl-suc-mon x₁))
... | inj₂ (inj₂ refl) | inj₁ x = refl
... | inj₂ (inj₁ x) | inj₂ (inj₁ x₁) = refl
... | inj₂ (inj₁ x) | inj₂ (inj₂ refl) = refl
... | inj₂ (inj₂ refl) | inj₂ (inj₁ x) = refl
... | inj₂ (inj₂ refl) | inj₂ (inj₂ refl) = refl

--! TF >

≤-trans : ∀ {i} {j} {k} → i ≤ j → j ≤ k → i ≤ k
≤-trans (inj₁ i<j) (inj₁ j<k) = inj₁ (<-trans-ℕ*ℕ i<j j<k)
≤-trans (inj₁ i<j) (inj₂ refl) = inj₁ i<j
≤-trans (inj₂ refl) j≤k = j≤k


<≤-trans : ∀ {i} {j} {k} → i <ℕ*ℕ j → j ≤ k → i <ℕ*ℕ k
<≤-trans i<j (inj₁ j<k) = <-trans-ℕ*ℕ i<j j<k
<≤-trans i<j (inj₂ refl) = i<j

≤-irrel : ∀ {i} {j} → (p q : i ≤ j) → p ≡ q
≤-irrel (inj₁ x) (inj₁ y) = cong inj₁ (<-irr _ _)
≤-irrel (inj₁ x) (inj₂ y) = ⊥-elim (<-irrefl-ℕ*ℕ y x)
≤-irrel (inj₂ y) (inj₁ x) = ⊥-elim (<-irrefl-ℕ*ℕ y x)
≤-irrel (inj₂ y) (inj₂ x) = cong inj₂ (≡-irrelevant-ℕ*ℕ y x)

-- level variable environments

LvlEnv = List ⊤

variable
      δ δ′ δ₁ δ₂ δ₃ : LvlEnv

data Mode : Set where
  <ω ≤ω : Mode

variable μ : Mode

module _ (δ : LvlEnv) where

  data MLvl : Mode → Set where
    `zero : MLvl <ω
    `suc  : MLvl μ → MLvl μ
    _`⊔_  : MLvl μ → MLvl μ → MLvl μ
    `_    : tt ∈ δ → MLvl <ω
    `fin  : MLvl <ω → MLvl ≤ω
    `omg  : ℕ → MLvl ≤ω
    
  FinLvl = MLvl <ω
  LimLvl = MLvl ≤ω

wkₗ  : MLvl δ μ → MLvl (tt ∷ δ) μ
wkₗ `zero      = `zero
wkₗ (`suc l)   = `suc (wkₗ l)
wkₗ (` x)      = ` (there x)
wkₗ (l₁ `⊔ l₂) = wkₗ l₁ `⊔ wkₗ l₂
wkₗ (`fin x) = `fin (wkₗ x)
wkₗ (`omg x) = `omg x

module these-hold-definitionally where
  wkₗ-⊔ : (l₁ l₂ : LimLvl δ) → wkₗ (l₁ `⊔ l₂) ≡ wkₗ l₁ `⊔ wkₗ l₂
  wkₗ-⊔ l₁ l₂ = refl

  wkₗ-suc : (l : LimLvl δ) → wkₗ (`suc l) ≡ `suc (wkₗ l)
  wkₗ-suc x = refl

-- semantics of finite levels
FLvl = ℕ

DEnv : LvlEnv → Set
DEnv δ = tt ∈ δ → FLvl

⟦_⟧ℓ : FinLvl δ → DEnv δ → FLvl
⟦ `zero ⟧ℓ d = ℕ.zero
⟦ `suc l ⟧ℓ d = ℕ.suc (⟦ l ⟧ℓ d)
⟦ l₁ `⊔ l₂ ⟧ℓ d = ⟦ l₁ ⟧ℓ d ⊔ℕ ⟦ l₂ ⟧ℓ d
⟦ ` x ⟧ℓ d = d x

⟦_⟧ℓ′ : LimLvl δ → DEnv δ → Lvl
⟦ `fin x ⟧ℓ′ d = ℕ.zero , ⟦ x ⟧ℓ d
⟦ x `⊔ y ⟧ℓ′ d = ⟦ x ⟧ℓ′ d ⊔ ⟦ y ⟧ℓ′ d
⟦ `suc x ⟧ℓ′ d = Lvl-suc (⟦ x ⟧ℓ′ d)
⟦ `omg k ⟧ℓ′ d = ω + (0 , k)

DEnv-ext : DEnv δ → FLvl → DEnv (tt ∷ δ)
DEnv-ext d ℓ (here refl) = ℓ
DEnv-ext d ℓ (there x) = d x

Lvl-fin : Lvl → Set
Lvl-fin (fst , snd) = fst ≡ ℕ.zero

variable l l′ l″ l₁ l₂ l₃ : LimLvl δ

-- level environments

--! Env
Env : LvlEnv → Set
Env δ = List (LimLvl δ)

wkₗₑ : Env δ → Env (tt ∷ δ)
wkₗₑ []      = []
wkₗₑ (l ∷ Δ) = wkₗ l ∷ wkₗₑ Δ


variable Δ Δ₁ Δ₂ Δ₃ : Env δ


--! Type

data Type δ (Δ : Env δ) : LimLvl δ → Set where

  `ℕ      : Type δ Δ (`fin `zero)
  _`⇒_    : (T₁ : Type δ Δ l₁) (T₂ : Type δ Δ l₂) → Type δ Δ (l₁ `⊔ l₂)
  `_      : (α : l ∈ Δ) → Type δ Δ l
  `∀α_,_  : (l : LimLvl δ) (T : Type δ (l ∷ Δ) l′) → Type δ Δ (`suc l `⊔ l′)
  `∀ℓ_    : (T : Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ l)) → Type δ Δ (`omg ℕ.zero `⊔ l)

Lᵈ : DEnv δ → LimLvl δ → Lvl
Lᵈ d l = ⟦ l ⟧ℓ′ d

Uᵈ : DEnv δ → LimLvl δ → Set
Uᵈ d l = U (Lᵈ d l)

⟦⟧ℓ-`⊔ : (d : DEnv δ) (l₁ l₂ : LimLvl δ) → ⟦ l₁ `⊔ l₂ ⟧ℓ′ d ≡ ⟦ l₁ ⟧ℓ′ d ⊔ ⟦ l₂ ⟧ℓ′ d
⟦⟧ℓ-`⊔ d l₁ l₂ = refl

⟦⟧ℓ-suc : (d : DEnv δ) (l : LimLvl δ) → ⟦ `suc l ⟧ℓ′ d ≡ Lvl-suc (⟦ l ⟧ℓ′ d)
⟦⟧ℓ-suc d x = refl

Lᵈ-⊔ : (d : DEnv δ) (l₁ : LimLvl δ) (l₂ : LimLvl δ) → Lᵈ d l₁ ⊔ Lᵈ d l₂ ≡ Lᵈ d (l₁ `⊔ l₂)
Lᵈ-⊔ d l₁ l₂ = refl

coef :  (d : DEnv δ) (x : FLvl) (fl : FinLvl δ) → ⟦ fl ⟧ℓ d ≡ ⟦ wkₗ fl ⟧ℓ  (DEnv-ext d x)
coef d x `zero = refl
coef d x (`suc fl) = cong ℕ.suc (coef d x fl)
coef d x (fl₁ `⊔ fl₂) = cong₂ _⊔ℕ_ (coef d x fl₁) (coef d x fl₂)
coef d x (` z) = refl

denv-wk-ext : (d : DEnv δ) (x : FLvl) (ll : LimLvl δ) → ⟦ ll ⟧ℓ′ d ≡ ⟦ wkₗ ll ⟧ℓ′ (DEnv-ext d x)
denv-wk-ext d x (`fin fl) = cong (ℕ.zero ,_) (coef d x fl)
denv-wk-ext d x (ll₁ `⊔ ll₂) = cong₂ _⊔_ (denv-wk-ext d x ll₁) (denv-wk-ext d x ll₂)
denv-wk-ext d x (`suc ll) = cong Lvl-suc (denv-wk-ext d x ll)
denv-wk-ext d x (`omg x₁) = refl

coel :  (d : DEnv δ) (x : FLvl) (ll : LimLvl δ) → Uᵈ d ll ≡ Uᵈ (DEnv-ext d x) (wkₗ ll)
coel d x ll = cong U (denv-wk-ext d x ll)



Env* : DEnv δ → Env δ → Set
Env* d Δ = All (Uᵈ d) Δ

coe* : {Δ : Env δ} (d : DEnv δ) (x : FLvl) → Env* d Δ → Env* (DEnv-ext d x) (wkₗₑ Δ)
coe* d x [] = []
coe* {Δ = ll ∷ _} d x (u ∷ η) = coe (coel d x ll) u ∷ coe* d x η



encode : (d : DEnv δ) (T : Type δ Δ l) (η : Env* d Δ) → Uᵈ d l
encode d `ℕ η = ℕ'
encode d (_`⇒_ {l₁ = l₁} {l₂ = l₂} T₁ T₂) η
  = (Lift≤ (⊔₁ (Lᵈ d l₁) (Lᵈ d l₂)) (encode d T₁ η))
    ⇒'
    (Lift≤ (⊔₂ (Lᵈ d l₁) (Lᵈ d l₂)) (encode d T₂ η))
encode d (` α) η = lookup η α
encode d (`∀α_,_ {l′ = l′} l T) η
  =
  let ≤-witness = ⊔₁ (⟦ `suc l ⟧ℓ′ d) (⟦ l′ ⟧ℓ′ d) in
  Π' (U' {j = ⟦ l ⟧ℓ′ d} (<≤-trans ℕ*ℕ-example.<suc ≤-witness))
     λ u → let r = encode d T (coe  (Uⁱʳ & ext (λ j → ext (λ p → cong (λ acc → (U< {⟦ l ⟧ℓ′ d} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) u ∷ η) in
         Lift≤ (⊔₂ (⟦ `suc l ⟧ℓ′ d) (⟦ l′ ⟧ℓ′ d)) r
encode d (`∀ℓ_ {l = l} T) η = Π' ℕ' (λ x → let r = coe (sym (coel d x l)) (encode (DEnv-ext d x) T (coe* d x η))
                                            in  Lift≤ (⊔₂ ω (Lᵈ d l)) r)


⟦_⟧ᵀ : (T : Type δ Δ l) (d : DEnv δ) → (η : Env* d Δ) → Set
⟦ T ⟧ᵀ d η = El (encode d T η)


-- type environments
data Ctx : ∀ {δ} → Env δ → Set where
  ∅     : Ctx {δ} []
  _◁_   : Type δ Δ l → Ctx Δ → Ctx Δ
  _◁*_  : (l : LimLvl δ) → Ctx Δ → Ctx (l ∷ Δ)
  ◁ℓ_   : Ctx Δ → Ctx (wkₗₑ Δ)

variable
  Γ Γ₁ Γ₂ Γ₂₁ Γ₂₂ : Ctx {δ} Δ
  T T′ : Type δ Δ l

postulate
  Twk : Type δ Δ l → Type δ (l′ ∷ Δ) l
  _[_]T : Type δ (l′ ∷ Δ) l → Type δ Δ l′ → Type δ Δ l
  _[_]ℓℓ : LimLvl (tt ∷ δ) → FinLvl δ → LimLvl δ
  _[_]ℓ : ∀ {l : LimLvl (tt ∷ δ)} → Type (tt ∷ δ) (wkₗₑ Δ) l → (newl : FinLvl δ) → Type δ Δ (l [ newl ]ℓℓ)

  wkₗₜ : Type δ Δ l → Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ l)

--! inn
data inn : Type δ Δ l → Ctx Δ → Set where
  here   : inn T (T ◁ Γ)
  there  : inn T Γ → inn T (T′ ◁ Γ)
  tskip  : inn T Γ → inn (Twk T) (l ◁* Γ)
  lskip  : inn T Γ → inn (wkₗₜ T) (◁ℓ Γ)


data Expr {δ} {Δ : Env δ} (Γ : Ctx Δ) : Type δ Δ l → Set where
  ##_    : (n : ℕ) → Expr Γ `ℕ
  `suc  : Expr Γ `ℕ → Expr Γ `ℕ
  `_    : ∀ {T : Type δ Δ l} → inn T Γ → Expr Γ T
  ƛ_    : ∀ {T : Type δ Δ l} {T′ : Type δ Δ l′} → Expr (T ◁ Γ) T′ → Expr Γ (T `⇒ T′)
  _·_   : ∀ {T : Type δ Δ l} {T′ : Type δ Δ l′} → Expr Γ (T `⇒ T′) → Expr Γ T → Expr Γ T′
  Λ_⇒_  : ∀ (l : LimLvl δ) → {T : Type δ (l ∷ Δ) l′} → Expr (l ◁* Γ) T → Expr Γ (`∀α l , T)
  _∙_    : ∀ {T : Type δ (l ∷ Δ) l′} → Expr Γ (`∀α l , T) → (T′ : Type δ Δ l) → Expr Γ (T [ T′ ]T)
  Λℓ_   : ∀ {T : Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ l)} → Expr (◁ℓ Γ) T → Expr Γ (`∀ℓ T)
  _·ℓ_  : ∀ {T : Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ l)} → Expr Γ (`∀ℓ T) → (newl : FinLvl δ) → Expr Γ (T [ newl ]ℓ)

variable e e₁ e₂ e₃ : Expr Γ T
variable n : ℕ

-- value environments

VEnv : {Δ : Env δ} → (d : DEnv δ) → Ctx Δ → Env* d Δ → Set
VEnv {δ} {Δ} d Γ η = ∀ l (T : Type δ Δ l) → (x : inn T Γ) → ⟦ T ⟧ᵀ d η

extend : ∀ {d : DEnv δ} {T : Type δ Δ l}{Γ : Ctx Δ}{η : Env* d Δ}
  → VEnv d Γ η → ⟦ T ⟧ᵀ d η → VEnv d (T ◁ Γ) η
extend γ v _ _ here = v
extend γ v _ _ (there x) = γ _ _ x

postulate
  extend-tskip : ∀ {d : DEnv δ} {Δ : Env δ} {Γ : Ctx Δ} {η : Env* d Δ} {⟦α⟧ : Uᵈ d l} →
    VEnv d Γ η → VEnv d (l ◁* Γ) (⟦α⟧ ∷ η)

  subst-env : ∀ {d : DEnv δ} (T : Type δ (l′ ∷ Δ) l) (T′ : Type δ Δ l′) (η : Env* d Δ) → ⟦ T ⟧ᵀ d (encode d T′ η ∷ η) ≡ ⟦ T [ T′ ]T ⟧ᵀ d η

  T-wk-ext : ∀ (d   : DEnv δ) (η   : Env* d Δ) (lev : FLvl) (T   : Type δ Δ l) → ⟦ T ⟧ᵀ d η ≡ ⟦ wkₗₜ T ⟧ᵀ (DEnv-ext d lev) (coe* d lev η)


postulate
  subst-lev-env : (newl : FinLvl δ) (d    : DEnv δ) (η    : Env* d Δ) (T    : Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ l))
    → ⟦ T ⟧ᵀ (DEnv-ext d (⟦ newl ⟧ℓ d)) (coe* d (⟦ newl ⟧ℓ d) η) ≡ ⟦ T [ newl ]ℓ ⟧ᵀ d η


crucial-equation : (l : LimLvl δ) (T : Type (tt ∷ δ) (wkₗₑ Δ) (wkₗ l)) (d : DEnv δ) (η : Env* d Δ) (x : FLvl)
  (code : Uᵈ (DEnv-ext d x) (wkₗ l))
    → El {Lᵈ d l} (coe (coel d x l ⁻¹) code)
    ≡ El {Lᵈ (DEnv-ext d x) (wkₗ l)} code
crucial-equation l T d η x code rewrite denv-wk-ext d x l = refl


coe** : {Γ : Ctx Δ} (d : DEnv δ) (η : Env* d Δ) (lev : FLvl) → VEnv d Γ η → VEnv (DEnv-ext d lev) (◁ℓ Γ) (coe* d lev η)
coe** d η lev γ .(wkₗ _) .(wkₗₜ T) (lskip{T = T} x) = coe (T-wk-ext d η lev T) (γ _ T x)

-- expression semantics

E⟦_⟧ : ∀ {T : Type δ Δ l}{Γ : Ctx Δ} → (e : Expr Γ T) (d : DEnv δ) (η : Env* d Δ) → (γ : VEnv d Γ η) → ⟦ T ⟧ᵀ d η
E⟦ ## n ⟧ d η γ = n
E⟦ `suc x ⟧ d η γ = ℕ.suc (E⟦ x ⟧ d η γ)
E⟦ ` x ⟧ d η γ = γ _ _ x
E⟦ ƛ_ {l = l₁}{l′ = l₂}{T = T₁}{T′ = T₂} M ⟧ d η γ
  = λ x → let r = E⟦ M ⟧ d η (extend γ (coe (ElLift≤ (⊔₁ (Lᵈ d l₁) (Lᵈ d l₂)) (encode d T₁ η)) x))
          in coe (sym (ElLift≤ (⊔₂ (Lᵈ d l₁) (Lᵈ d l₂)) (encode d T₂ η))) r
E⟦ _·_ {l = l}{l′ = l′}{T = T}{T′ = T′} M N ⟧ d η γ =
  let f = E⟦ M ⟧ d η γ ; a = E⟦ N ⟧ d η γ in
  coe (ElLift≤ (⊔₂ (Lᵈ d l) (Lᵈ d l′)) (encode d T′ η)) (f (coe (sym (ElLift≤ (⊔₁ (Lᵈ d l) (Lᵈ d l′)) (encode d T η))) a))
-- E⟦ M ⟧ η γ (E⟦ N ⟧ η γ)
E⟦ Λ_⇒_ {l′ = l′} l {T} M ⟧ d η γ = λ α →
  let η′ = coe (Uⁱʳ & ext (λ j → ext (λ p → cong (λ acc → (U< {Lᵈ d l} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) α ∷ η in
  let r = E⟦ M ⟧ d η′ (extend-tskip γ) in
  coe (sym (ElLift≤ (⊔₂ (Lᵈ d (`suc l)) (Lᵈ d l′)) (encode d T η′))) r
-- E⟦ M ⟧ (α ∷ η) (extend-tskip γ)
E⟦ _∙_ {l = l} {l′ = l′}{T = T} M T′ ⟧ d η γ =
  let F = E⟦ M ⟧ d η γ in
  let u′ = encode d T′ η in
  let eq1 = (Uⁱʳ & ext (λ j → ext (λ p → cong (λ acc → (U< {Lᵈ d l} ⦃ acc ⦄ j p)) (Acc-prop _ wf)))) in
  let eq2 = Uⁱʳ & (ext (λ j → ext (λ p → trans (U<-compute {Lᵈ d l} {wf} {j} {p}) (sym U<-compute)))) in
  let r = F (coe eq2 u′) in
  coe (trans (trans (cong (λ □ → Elⁱʳ (Lift≤ (⊔₂ (Lᵈ d (`suc l)) (Lᵈ d l′)) (encode d T (□ ∷ η)))) (coe-coe eq2 eq1 {u′}))
                    (ElLift≤ (⊔₂ (Lᵈ d (`suc l)) (Lᵈ d l′)) (encode d T (u′ ∷ η)))) (subst-env T T′ η)) r

E⟦ Λℓ_ {l = l}{T = T} M ⟧ d η γ =
  λ x → let r = E⟦ M ⟧ (DEnv-ext d x) (coe* d x η) (coe** d η x γ) in
        coe (sym (trans
                    (ElLift≤ (⊔₂ ω (Lᵈ d l)) (coe (coel d x l ⁻¹) (encode (DEnv-ext d x) T (coe* d x η))))
                    (crucial-equation l T d η x (encode (DEnv-ext d x) T (coe* d x η)))
                    )) r

E⟦ _·ℓ_ {l = l}{T = T} M newl ⟧ d η γ =
  let r = E⟦ M ⟧ d η γ in
  let x = ⟦ newl ⟧ℓ d in
  coe (trans
         (ElLift≤ (⊔₂ ω (Lᵈ d l)) (coe (coel d x l ⁻¹) (encode (DEnv-ext d x) T (coe* d x η))))
         (trans (crucial-equation l T d η x (encode (DEnv-ext d x) T (coe* d x η)))
                (subst-lev-env newl d η T))) (r x)
