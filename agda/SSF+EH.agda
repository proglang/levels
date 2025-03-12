module SSF+EH where

open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open import Level using (Level; Lift; lift; zero; suc; _⊔_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ) 
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_) 
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; icong; subst)
open import Function using (_∘_; id; flip; _$_)
open import ExtendedHierarchy using (𝟎; 𝟏; ω; ω²; ⌊_⌋; cast; cast-intro; cast-elim; β-suc-zero; β-suc-ω; β-suc-⌊⌋; ω^_+_;  <₁; <₂; <₃; MutualOrd)
open import BoundedQuantification using (BoundedLevel; BoundedLift; bounded-lift; bounded-unlift; _,_; #_; #<Λ; _<_; _≤_; ≤-id; ≤-suc; ≤-lub; ≤-add; ≤-exp; ≤-lublub; <-suc-lim; lim)

--! XH >

coe : ∀ {ℓ}{A B : Set ℓ} → A ≡ B → A → B
coe = subst id

variable
  o : MutualOrd

-- bounds of level variables
LEnv = List MutualOrd

variable
  δ δ′ δ₁ δ₂ δ₃ : LEnv

data Lvl (δ : LEnv) : Set where 
  `_    : o ∈ δ → Lvl δ
  `suc  : Lvl δ → Lvl δ
  _`⊔_  : Lvl δ → Lvl δ → Lvl δ
  ⟨_⟩   : Level → Lvl δ
      
variable
  l l′ l₁ l₂ l₃ : Lvl δ

Lwk  : Lvl δ → Lvl (o ∷ δ)
Lwk (` x) = ` there x
Lwk (`suc l) = `suc (Lwk l)
Lwk (l₁ `⊔ l₂) = Lwk l₁ `⊔ Lwk l₂
Lwk ⟨ x ⟩ = ⟨ x ⟩


_[_]L : Lvl (o ∷ δ) → Lvl δ → Lvl δ
(` here px) [ l′ ]L = l′
(` there x) [ l′ ]L = ` x
`suc l [ l′ ]L = `suc (l [ l′ ]L)
(l₁ `⊔ l₂) [ l′ ]L = (l₁ [ l′ ]L) `⊔ (l₂ [ l′ ]L)
⟨ x ⟩ [ l′ ]L = ⟨ x ⟩

variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : BoundedLevel ⌊ ω ⌋

--! LEnvSem
⟦_⟧δ : (δ : LEnv) → Set
⟦ []    ⟧δ = ⊤
⟦ o ∷ δ ⟧δ = BoundedLevel ⌊ o ⌋ × ⟦ δ ⟧δ
    
variable
  κ κ′ κ₁ κ₂ κ₃ : ⟦ δ ⟧δ

_∷κ_ : BoundedLevel ⌊ o ⌋ → ⟦ δ ⟧δ → ⟦ o ∷ δ ⟧δ
_∷κ_ = _,_

lookup-κ : ⟦ δ ⟧δ → o ∈ δ → BoundedLevel ⌊ o ⌋
lookup-κ {_ ∷ δ} (ℓ , κ) (here refl) = ℓ
lookup-κ {_ ∷ δ} (ℓ , κ) (there x)   = lookup-κ κ x

drop-κ : ⟦ o ∷ δ ⟧δ → ⟦ δ ⟧δ
drop-κ (_ , κ) = κ

-- the subst in the definition of 0<ω would be gone if EH be part of agda
--! zeroLtomega
-- 0<ω : zero < ω^ zero + zero
-- 0<ω = subst (suc zero ≤_) β-suc-zero (≤-id (suc zero))

⟦_⟧L : Lvl δ → ⟦ δ ⟧δ → Level
⟦ ` x ⟧L κ = # lookup-κ κ x
⟦ `suc l ⟧L κ = suc (⟦ l ⟧L κ)
⟦ l₁ `⊔ l₂ ⟧L κ = ⟦ l₁ ⟧L κ ⊔ ⟦ l₂ ⟧L κ
⟦ ⟨ x ⟩ ⟧L κ = x 

postulate
  ≤-sucsuc : ∀ {ℓ₁ ℓ₂ : Level} → ℓ₁ ≤ ℓ₂ → suc ℓ₁ ≤ suc ℓ₂

⟦_⟧LP : (l : Lvl δ) → (κ : ⟦ δ ⟧δ) → ∃[ ℓ ] ⟦ l ⟧L κ < ℓ
⟦ `_ {o = o} x ⟧LP κ = ⌊ o ⌋ , #<Λ (lookup-κ κ x)
⟦ `suc l ⟧LP κ
  with ⟦ l ⟧LP κ
... | fst , p = suc fst , ≤-sucsuc p 
⟦ l₁ `⊔ l₂ ⟧LP κ
  with ⟦ l₁ ⟧LP κ | ⟦ l₂ ⟧LP κ
... | ℓ₁ , p₁ | ℓ₂ , p₂ = ℓ₁ ⊔ ℓ₂ , ≤-lublub (≤-lub ℓ₁ p₂) (≤-lub ℓ₂ p₁)
⟦ ⟨ x ⟩ ⟧LP κ = suc x , ≤-id (suc x)


postulate
  ⟦Lwk⟧L : ∀ (l : Lvl δ) (κ : ⟦ δ ⟧δ) (ℓ : BoundedLevel ⌊ o ⌋) → 
    ⟦ Lwk{o = o} l ⟧L (_∷κ_ {o = o} ℓ κ) ≡ ⟦ l ⟧L κ
  ⟦[]L⟧L : ∀ (l : Lvl (o ∷ δ)) (κ : ⟦ δ ⟧δ) (l′ : Lvl δ) (p : ⟦ l′ ⟧L κ < ⌊ o ⌋) → 
    ⟦ l [ l′ ]L ⟧L κ ≡ ⟦ l ⟧L (((⟦ l′ ⟧L κ) , p) , κ)
  -- ⟦[]L⟧L : ∀ (l : Lvl (o ∷ δ)) (κ : ⟦ δ ⟧δ) l′ → 
  --   ⟦ l [ l′ ]L ⟧L κ ≡ ⟦ l ⟧L (⟦ l′ ⟧L κ , κ)

data TEnv : LEnv → Set where
  []   : TEnv δ
  _∷_  : Lvl δ → TEnv δ → TEnv δ 
  ∷l_  : TEnv δ → TEnv (o ∷ δ) 

variable
  Δ Δ′ Δ₁ Δ₂ Δ₃ : TEnv δ

suc⨆Δ :  ⟦ δ ⟧δ → TEnv δ → Level
suc⨆Δ κ []      = zero
suc⨆Δ κ (l ∷ Δ) = suc (⟦ l ⟧L κ) ⊔ suc⨆Δ κ Δ  
suc⨆Δ κ (∷l_ {o = o} Δ)  = suc⨆Δ (drop-κ {o = o} κ) Δ 

data _∍_ : TEnv δ → Lvl δ → Set where
  here  : (l ∷ Δ) ∍ l
  there : Δ ∍ l → (l′ ∷ Δ) ∍ l
  lskip : Δ ∍ l → (∷l Δ) ∍ Lwk {o = o} l

data Type (Δ : TEnv δ) : Lvl δ → Set where
  Nat   : Type Δ ⟨ zero ⟩
  `_    : Δ ∍ l → Type Δ l
  _⇒_   : Type Δ l₁ → Type Δ l₂ → Type Δ (l₁ `⊔ l₂) 
  ∀α    : Type (l ∷ Δ) l′ → Type Δ (`suc l `⊔ l′) 
  ∀ℓ    : (o : MutualOrd) (p : zero <  ⌊ o ⌋) → Type (∷l Δ) (Lwk {o = o} l) → Type Δ (⟨ ⌊ o ⌋ ⟩ `⊔ l)
--   conv  : Type Δ l → (∀ κ → ⟦ l ⟧L κ ≡ ⟦ l′ ⟧L κ) → Type Δ l′

-- data Type (Δ : TEnv δ) : (⟦ δ ⟧δ → Level) → Set where
--   Nat   : Type Δ λ κ → zero
--   `_    : Δ ∍ l → Type Δ ⟦ l ⟧L
--   _⇒_   : ∀ {f₁ f₂} → Type Δ f₁ → Type Δ f₂ → Type Δ λ κ → f₁ κ ⊔ f₂ κ
--   ∀α    : ∀ {f′} → Type (l ∷ Δ) f′ → Type Δ λ κ → suc (⟦ l ⟧L κ) ⊔ f′ κ
--   ∀ℓ    : (o : MutualOrd) (p : zero < ⌊ o ⌋) → {f : ⟦ o ∷ δ ⟧δ → Level}
--         → Type (∷l_ {o = o} Δ) f → Type Δ λ κ → ⌊ o ⌋ ⊔ f ((zero , p) , κ)

-- -- examples

-- _ : Type {δ = []} [] λ κ → suc zero
-- _ = ∀α {l = ⟨ zero ⟩} (` here)

-- _ : Type {δ = []} [] λ κ → suc zero
-- _ = ∀α {l = ⟨ zero ⟩} ((` here) ⇒ (` here))
      
      
variable
  μ μ′ : ⟦ δ ⟧δ → Level
  T T′ T₁ T₂ T₃ : Type Δ l

postulate
  TTwk : Type Δ l′ → Type (l ∷ Δ) l′
  TLwk : Type Δ l → Type (∷l_ {o = o} Δ) (Lwk l)
  _[_]TT : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
  _[_]TL : Type (∷l Δ) l → (l′ : Lvl δ) → Type Δ ( l [ l′ ]L )
       
--! FTSEAsFunction
⟦_⟧Δ : (Δ : TEnv δ) → (κ : ⟦ δ ⟧δ) → Set (suc⨆Δ κ Δ)
⟦  []    ⟧Δ κ  = ⊤
⟦ l ∷ Δ  ⟧Δ κ  = Set (⟦ l ⟧L κ) × ⟦ Δ ⟧Δ κ
⟦ ∷l_ {o = o} Δ   ⟧Δ κ  = ⟦ Δ ⟧Δ (drop-κ {o = o} κ)

_∷η_ : {κ : ⟦ δ ⟧δ} → Set (⟦ l ⟧L κ) → ⟦ Δ ⟧Δ κ → ⟦ l ∷ Δ ⟧Δ κ
_∷η_ = _,_

lookup-η : {κ : ⟦ δ ⟧δ} → ⟦ Δ ⟧Δ κ → Δ ∍ l → Set (⟦ l ⟧L κ) 
lookup-η (A , _) here                    = A
lookup-η (_ , η) (there x)               = lookup-η η x
lookup-η {κ = ℓ , κ} η (lskip {l = l}{o = o} x) = cast (sym (⟦Lwk⟧L {o = o} l κ ℓ)) (lookup-η η x)

drop-η : {κ : ⟦ δ ⟧δ} → ⟦ l ∷ Δ ⟧Δ κ → ⟦ Δ ⟧Δ κ 
drop-η (_ , η) = η

--! TSem
⟦_⟧T : {Δ : TEnv δ} → (T : Type Δ l) → (κ : ⟦ δ ⟧δ) → ⟦ Δ ⟧Δ κ → Set (⟦ l ⟧L κ)
⟦ Nat      ⟧T κ η  = ℕ
⟦ ` α      ⟧T κ η  = lookup-η η α
⟦ T₁ ⇒ T₂  ⟧T κ η  = ⟦ T₁ ⟧T κ η → ⟦ T₂ ⟧T κ η   
⟦_⟧T {Δ = Δ} (∀α {l = l} T) κ η = ∀ A → 
  let η′ = _∷η_ {l = l} {Δ = Δ} {κ = κ} A η in
  ⟦ T ⟧T κ η′
⟦_⟧T {l = l} {Δ = Δ} (∀ℓ {l = l₁} o p T) κ η = ∀ (ℓ : BoundedLevel ⌊ o ⌋) →
  cast (cong (⌊ o ⌋ ⊔_) (⟦Lwk⟧L {o = o} l₁ κ ℓ))
       (Lift ⌊ o ⌋ (⟦ T ⟧T (_∷κ_ {o = o} ℓ κ) η))

postulate
  ⟦TLwk⟧T : {Δ : TEnv δ} {T : Type Δ l} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} {ℓ : BoundedLevel ⌊ o ⌋} →
    ⟦ T ⟧T κ η ≡ cast (⟦Lwk⟧L {o = o} l κ ℓ) (⟦ TLwk {o = o} T ⟧T (ℓ , κ) η) 
  ⟦TTwk⟧T : {Δ : TEnv δ} {T : Type Δ l} {κ : ⟦ δ ⟧δ} {A : Set (⟦ l′ ⟧L κ)} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ T ⟧T κ η ≡ ⟦ TTwk {l = l′} T ⟧T κ (A , η)

  ⟦[]LT⟧T : {T : Type (∷l_ {o = o} Δ) (Lwk l)} {l′ : Lvl δ} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} {p : ⟦ l′ ⟧L κ < ⌊ o ⌋} →  
    ⟦ T ⟧T ((⟦ l′ ⟧L κ , p) , κ) η ≡ cast (⟦[]L⟧L {o = o} (Lwk l) κ l′ p) (⟦ T [ l′ ]TL ⟧T κ η)
  ⟦[]TT⟧T : {l′ : Lvl δ} {T : Type (l′ ∷ Δ) l} {T′ : Type Δ l′} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ T ⟧T κ (_∷η_ {l = l′} {Δ = Δ} {κ = κ} (⟦ T′ ⟧T κ η) η) ≡ ⟦ T [ T′ ]TT ⟧T κ η
    
data EEnv : (Δ : TEnv δ) → Set where
  []   : EEnv Δ
  _∷_  : Type Δ l → EEnv Δ → EEnv Δ
  _∷l_ : (l : Lvl δ) → EEnv Δ → EEnv (l ∷ Δ)
  ∷ol : {o : MutualOrd} → EEnv Δ → EEnv (∷l_ {o = o} Δ)

variable
  Γ Γ′ Γ₁ Γ₂ Γ₃ : EEnv Δ

data _∋_ : EEnv Δ → Type Δ l → Set where
  here  : (T ∷ Γ) ∋ T
  there : Γ ∋ T → (T′ ∷ Γ) ∋ T
  tskip : Γ ∋ T → (l ∷l Γ) ∋ TTwk T
  lskip : Γ ∋ T → (∷ol {o = o} Γ) ∋ TLwk T

⨆Γ : ∀ {Δ : TEnv δ} → EEnv Δ → ⟦ δ ⟧δ → Level
⨆Γ []                κ = zero 
⨆Γ (_∷_ {l = l} T Γ) κ = ⟦ l ⟧L κ  ⊔ ⨆Γ Γ κ 
⨆Γ (ℓ ∷l Γ)          κ = ⨆Γ Γ κ
⨆Γ (∷ol {o = o} Γ)            κ = ⨆Γ Γ (drop-κ {o = o} κ)


data Expr {Δ : TEnv δ} (Γ : EEnv Δ) : Type Δ l → Set where
  `_    : Γ ∋ T → Expr Γ T
  #    : ℕ → Expr Γ Nat
  ‵suc  : Expr Γ Nat → Expr Γ Nat
  λx_   : Expr (T ∷ Γ) T′ → Expr Γ (T ⇒ T′)
  Λ_⇒_  : (l : Lvl δ) {T : Type (l ∷ Δ) l′} → Expr (l ∷l Γ) T → Expr Γ (∀α T)
  Λℓ<_⇒_ : {o : MutualOrd} (p : zero < ⌊ o ⌋) {T : Type (∷l Δ) (Lwk {o = o} l)}
         → Expr (∷ol Γ) T → Expr Γ (∀ℓ o p T)
  _·_   : Expr Γ (T₁ ⇒ T₂) → Expr Γ T₁ → Expr Γ T₂
  _∙_   : Expr Γ (∀α T) → (T′ : Type Δ l) → Expr Γ (T [ T′ ]TT) 
  _∙ℓ_[_]  : {p : zero < ⌊ o ⌋} {T : Type (∷l Δ) (Lwk l)}
           → Expr Γ (∀ℓ o p T) → (l′ : Lvl δ) → (∀ κ → ⟦ l′ ⟧L κ < ⌊ o ⌋) → Expr Γ (T [ l′ ]TL)
  -- should we have a syntax for such proofs?

⟦_⟧Γ   : {Δ : TEnv δ} → (Γ : EEnv Δ) → (κ : ⟦ δ ⟧δ) → ⟦ Δ ⟧Δ κ → Set (⨆Γ Γ κ)
⟦ []     ⟧Γ κ η = ⊤
⟦ T ∷ Γ  ⟧Γ κ η = ⟦ T ⟧T κ η × ⟦ Γ ⟧Γ κ η
⟦_⟧Γ {Δ = l ∷ Δ} (l ∷l Γ) κ η = ⟦ Γ ⟧Γ κ (drop-η {l = l} {Δ = Δ} {κ = κ} η) 
⟦ ∷ol {o = o} Γ   ⟧Γ κ η = ⟦ Γ ⟧Γ (drop-κ {o = o} κ) η 
   
_∷γ_ : {Δ : TEnv δ} {T : Type Δ l} {Γ : EEnv Δ} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ T ⟧T κ η → ⟦ Γ ⟧Γ κ η → ⟦ T ∷ Γ ⟧Γ κ η
_∷γ_ = _,_

lookup-γ : {Δ : TEnv δ} {Γ : EEnv Δ} {T : Type Δ l} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ Γ ⟧Γ κ η → Γ ∋ T → ⟦ T ⟧T κ η 
lookup-γ (A , γ) here       = A
lookup-γ (_ , γ) (there x)  = lookup-γ γ x
lookup-γ {Γ = _ ∷l Γ} {κ = κ} {η = A , η} γ (tskip {T = T} x) = 
  coe ⟦TTwk⟧T (lookup-γ γ x)
lookup-γ {δ = o ∷ δ} {Γ = ∷ol Γ} {κ = A , κ} {η = η} γ (lskip x) = 
  cast-elim _ (coe ⟦TLwk⟧T (lookup-γ {δ = δ} {κ = κ} γ x))

--! ESem
⟦_⟧E : {Δ : TEnv δ} {T : Type Δ l} {Γ : EEnv Δ} → 
  Expr Γ T → (κ : ⟦ δ ⟧δ) (η : ⟦ Δ ⟧Δ κ) → ⟦ Γ ⟧Γ κ η → ⟦ T ⟧T κ η
⟦ ` x     ⟧E κ η γ = lookup-γ γ x
⟦ # n     ⟧E κ η γ = n
⟦ ‵suc e  ⟧E κ η γ = ℕ.suc (⟦ e ⟧E κ η γ)
⟦_⟧E {T = T₁ ⇒ T₂} {Γ} (λx e) κ η γ = λ x →
  let γ′ = _∷γ_ {T = T₁} {Γ = Γ} x γ in
  ⟦ e ⟧E κ η γ′
⟦ e₁ · e₂ ⟧E κ η γ = ⟦ e₁ ⟧E κ η γ (⟦ e₂ ⟧E κ η γ)
⟦_⟧E {Δ = Δ} (Λ l ⇒ e) κ η γ = λ A → 
  let η′ = _∷η_ {l = l} {Δ = Δ} {κ = κ} A η in 
  ⟦ e ⟧E κ η′ γ
⟦ e ∙ T′ ⟧E κ η γ = coe ⟦[]TT⟧T (⟦ e ⟧E κ η γ (⟦ T′ ⟧T κ η)) 
⟦ Λℓ<_⇒_ {o = o} p e ⟧E κ η γ = λ ℓ → 
  cast-intro _ (lift {ℓ = ⌊ o ⌋} (⟦ e ⟧E (_∷κ_ {o = o} ℓ κ) η γ))
⟦ _∙ℓ_[_] {o = o}{l = l} e l′ p′ ⟧E κ η γ = 
  cast-elim _ (coe (⟦[]LT⟧T {o = o}{p = p′ κ}) (Lift.lower (cast-elim _ (⟦ e ⟧E κ η γ (⟦ l′ ⟧L κ , p′ κ)))))
