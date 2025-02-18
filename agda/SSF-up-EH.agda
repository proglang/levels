module SSF-up-EH where

open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open import Level using (Level; Lift; lift; zero; suc; _⊔_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ) 
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_) 
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Function using (_∘_; id; flip; _$_)
open import ExtendedHierarchy using (𝟎; 𝟏; ω; ω+ₙ_; ⌊_⌋; cast; β-suc-zero; β-suc-ω; β-suc-⌊⌋; ω^_+_;  <₁; <₂; <₃)
open import BoundQuantification using (BoundLevel; BoundLift; bound-lift; bound-unlift; _,_; #; #<Λ; _<_; <₀; <₁; <₂; <₃)

postulate
  fun-ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂

dep-ext : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {F G : (a : A) → Set ℓ₂} → 
  ((a : A) → F a ≡ G a) → ((a : A) → F a) ≡ ((a : A) → G a) 
dep-ext = ∀-extensionality fun-ext _ _

LEnv = List ⊤

variable
  δ δ′ δ₁ δ₂ δ₃ : LEnv

data LivesIn : Set where
  <ω : LivesIn
  <ω> : LivesIn

variable
  μ μ′ μ₁ μ₂ μ₃ : LivesIn
    
data Lvl (δ : LEnv) : LivesIn → Set where 
  `zero  : Lvl δ <ω
  `suc   : Lvl δ μ → Lvl δ μ
  `_     : tt ∈ δ → Lvl δ <ω
  _`⊔_   : Lvl δ <ω → Lvl δ <ω → Lvl δ <ω
  _``⊔_  : Lvl δ μ₁ → Lvl δ μ₂ → Lvl δ <ω>
  `ω    : Lvl δ <ω>

↑_ : Lvl δ <ω → Lvl δ <ω> 
↑ l = l ``⊔ l 
      
variable
  l l′ l₁ l₂ l₃ : Lvl δ μ

LRen : LEnv → LEnv → Set
LRen δ₁ δ₂ = tt ∈ δ₁ → tt ∈ δ₂

Lidᵣ : LRen δ δ
Lidᵣ = id

Ldropᵣ : LRen (tt ∷ δ₁) δ₂ → LRen δ₁ δ₂
Ldropᵣ ρ x = ρ (there x)

Lwkᵣ : LRen δ₁ δ₂ → LRen δ₁ (tt ∷ δ₂)
Lwkᵣ ρ x = there (ρ x)

Lliftᵣ : LRen δ₁ δ₂ →  LRen (tt ∷ δ₁) (tt ∷ δ₂)
Lliftᵣ ρ (here refl) = here refl
Lliftᵣ ρ (there x)   = there (ρ x)

Lren : LRen δ₁ δ₂ → Lvl δ₁ μ → Lvl δ₂ μ
Lren ρ `zero       = `zero
Lren ρ (`suc l)    = `suc (Lren ρ l)
Lren ρ (` x)       = ` ρ x
Lren ρ (l₁ `⊔ l₂)  = Lren ρ l₁ `⊔ Lren ρ l₂
Lren ρ (l₁ ``⊔ l₂) = Lren ρ l₁ ``⊔ Lren ρ l₂
Lren ρ `ω          = `ω

Lwk  : Lvl δ μ → Lvl (tt ∷ δ) μ
Lwk = Lren (Lwkᵣ Lidᵣ)  

LSub : LEnv → LEnv → Set
LSub δ₁ δ₂ = tt ∈ δ₁ → Lvl δ₂ <ω 

Lidₛ : LSub δ δ
Lidₛ = `_

Ldropₛ : LSub (tt ∷ δ₁) δ₂ → LSub δ₁ δ₂
Ldropₛ σ x = σ (there x)

Lwkₛ : LSub δ₁ δ₂ → LSub δ₁ (tt ∷ δ₂)
Lwkₛ σ x = Lwk (σ x)

Lliftₛ : LSub δ₁ δ₂ → LSub (tt ∷ δ₁) (tt ∷ δ₂)
Lliftₛ σ (here refl) = ` (here refl)
Lliftₛ σ (there x)   = Lwk (σ x)

Lsub : LSub δ₁ δ₂ → Lvl δ₁ μ → Lvl δ₂ μ
Lsub σ `zero      = `zero
Lsub σ (`suc l)   = `suc (Lsub σ l)
Lsub σ (` x)      = σ x
Lsub σ (l₁ `⊔ l₂) = Lsub σ l₁ `⊔ Lsub σ l₂
Lsub σ (l₁ ``⊔ l₂) = Lsub σ l₁ ``⊔ Lsub σ l₂
Lsub σ `ω         = `ω

Lextₛ : LSub δ₁ δ₂ → Lvl δ₂ <ω → LSub (tt ∷ δ₁) δ₂
Lextₛ σ l′ (here refl) = l′
Lextₛ σ l′ (there x)   = σ x

_[_]LL : Lvl (tt ∷ δ) μ → Lvl δ <ω → Lvl δ μ
l [ l′ ]LL = Lsub (Lextₛ Lidₛ l′) l

⟦_⟧δ : (δ : LEnv) → Set
⟦ []    ⟧δ = ⊤
⟦ x ∷ δ ⟧δ = BoundLevel ⌊ ω ⌋ × ⟦ δ ⟧δ

variable
  κ κ′ κ₁ κ₂ κ₃ : ⟦ δ ⟧δ
    
[]κ : ⟦ [] ⟧δ
[]κ = tt

_∷κ_ : BoundLevel ⌊ ω ⌋ → ⟦ δ ⟧δ → ⟦ tt ∷ δ ⟧δ
_∷κ_ = _,_

lookup-κ : ⟦ δ ⟧δ → tt ∈ δ → Level
lookup-κ {_ ∷ δ} (ℓ , κ) (here refl) = # ℓ
lookup-κ {_ ∷ δ} (ℓ , κ) (there x)   = lookup-κ κ x

drop-κ : ⟦ tt ∷ δ ⟧δ → ⟦ δ ⟧δ
drop-κ (_ , κ) = κ

⟦_⟧L : ∀ {δ : LEnv} → (l : Lvl δ μ) → ⟦ δ ⟧δ → Level
⟦ `zero     ⟧L κ = zero
⟦ `suc l    ⟧L κ = suc (⟦ l ⟧L κ)
⟦ ` x       ⟧L κ = lookup-κ κ x
⟦ l₁ `⊔ l₂  ⟧L κ = (⟦ l₁ ⟧L κ) ⊔ (⟦ l₂ ⟧L κ)
⟦ l₁ ``⊔ l₂ ⟧L κ = (⟦ l₁ ⟧L κ) ⊔ (⟦ l₂ ⟧L κ)
⟦ `ω        ⟧L κ = ⌊ ω ⌋

⟦_⟧L′ : ∀ {δ : LEnv} → Lvl δ <ω → ⟦ δ ⟧δ → BoundLevel ⌊ ω ⌋
⟦ `zero    ⟧L′ κ = zero , {!  !}
⟦ `suc l   ⟧L′ κ = (suc (# (⟦ l ⟧L′ κ))) , {! #<Λ (⟦ l ⟧L′ κ) !}
⟦ ` x      ⟧L′ κ = lookup-κ κ x , {!   !}
⟦ l₁ `⊔ l₂ ⟧L′ κ = # (⟦ l₁ ⟧L′ κ) ⊔ # (⟦ l₂ ⟧L′ κ) , {!   !}

⟦Lwk⟧L-drop : ∀ (l : Lvl δ μ) κ → ⟦ Lwk l ⟧L κ ≡ ⟦ l ⟧L (drop-κ κ)
⟦Lwk⟧L-drop  l    κ = {!   !}
⟦Lwk⟧L-∷κ : ∀ (l : Lvl δ μ) κ (ℓ : BoundLevel ⌊ ω ⌋) → ⟦ Lwk l ⟧L (ℓ ∷κ κ) ≡ ⟦ l ⟧L κ
⟦Lwk⟧L-∷κ  l      κ ℓ = {!   !}

data TEnv : LEnv → Set where
  []   : TEnv δ
  _∷_  : (l : Lvl δ μ) → TEnv δ → TEnv δ 
  ∷l_  : TEnv δ → TEnv (tt ∷ δ) 

variable
  Δ Δ′ Δ₁ Δ₂ Δ₃ : TEnv δ

suc⨆Δ :  {δ : LEnv} → ⟦ δ ⟧δ → TEnv δ → Level
suc⨆Δ κ []      = zero
suc⨆Δ κ (l ∷ Δ) = suc (⟦ l ⟧L κ) ⊔ suc⨆Δ κ Δ  
suc⨆Δ κ (∷l Δ)  = suc⨆Δ (drop-κ κ) Δ  

data _∍_ : TEnv δ → Lvl δ μ → Set where
  here  : (l ∷ Δ) ∍ l
  there : Δ ∍ l → (l′ ∷ Δ) ∍ l
  lskip : Δ ∍ l → (∷l Δ) ∍ Lwk l

data Type {δ : LEnv} (Δ : TEnv δ) : Lvl δ μ → Set where
  Nat   : Type Δ `zero
  `_    : Δ ∍ l → Type Δ l
  _⇒_   : Type Δ l₁ → Type Δ l₂ → Type Δ (l₁ `⊔ l₂) 
  ∀α    : {l : Lvl δ <ω>} → Type (l ∷ Δ) l′ → Type Δ (`suc l ``⊔ l′) 
  ∀ℓ    : Type (∷l Δ) (Lwk l) → Type Δ (`ω ``⊔ l)
      
pattern ∀α:_⇒_ l {l′ = l′} T = ∀α {l = l} {l′ = l′} T

variable
  T T′ T₁ T₂ T₃ : Type Δ l

TRen : TEnv δ → TEnv δ → Set
TRen {δ} Δ₁ Δ₂ = ∀ μ (l : Lvl δ μ) → Δ₁ ∍ l → Δ₂ ∍ l

Tidᵣ : TRen Δ Δ
Tidᵣ _ _ = id

TTdropᵣ : TRen (l ∷ Δ₁) Δ₂ → TRen Δ₁ Δ₂
TTdropᵣ ρ _ _ x = ρ _ _ (there x)

Twkᵣ : TRen Δ₁ Δ₂ → TRen Δ₁ (l ∷ Δ₂)
Twkᵣ ρ _ _ x = there (ρ _ _ x)

TTliftᵣ : TRen Δ₁ Δ₂ → ∀ (l : Lvl δ μ) → TRen (l ∷ Δ₁) (l ∷ Δ₂)
TTliftᵣ ρ _ _ _ (here)      = here
TTliftᵣ ρ _ _ _ (there x)   = there (ρ _ _ x)

TLliftᵣ : TRen Δ₁ Δ₂ → TRen (∷l Δ₁) (∷l Δ₂)
TLliftᵣ ρ _ _ (lskip x) = lskip (ρ _ _ x)

TTren : TRen Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
TTren ρ Nat       = Nat
TTren ρ (` x)     = ` ρ _ _ x
TTren ρ (T₁ ⇒ T₂) = TTren ρ T₁ ⇒ TTren ρ T₂
TTren ρ (∀α T)    = ∀α (TTren (TTliftᵣ ρ _) T)
TTren ρ (∀ℓ T)    = ∀ℓ (TTren (TLliftᵣ ρ) T)

-- Δren : LRen δ₁ δ₂ → TEnv δ₁ → TEnv δ₂
-- Δren ρ []      = []
-- Δren ρ (l ∷ Δ) = Lren ρ l ∷ Δren ρ Δ
-- Δren ρ (∷l Δ)  = Δren (Ldropᵣ ρ) Δ

postulate 
  TLren : {Δ₁ : TEnv δ₁} (ρ : LRen δ₁ δ₂) → 
    Type Δ₁ l → Type (Δren ρ Δ₁) (Lren ρ l) 
-- TLren ρ Nat       = Nat
-- TLren ρ (` x)     = ` TLren` ρ x
--   where TLren` : {Δ₁ : TEnv δ₁} (ρ : LRen δ₁ δ₂) →  Δ₁ ∍ l → (Δren ρ Δ₁) ∍ (Lren ρ l) 
--         TLren` ρ here      = here
--         TLren` ρ (there x) = there (TLren` ρ x)
--         TLren` ρ (lskip x) = {! TLren` (Ldropᵣ ρ) x !} 
-- TLren ρ (T₁ ⇒ T₂) = (TLren ρ T₁) ⇒ TLren ρ T₂
-- TLren ρ (∀α T)    = ∀α (TLren ρ T)
-- TLren ρ (∀ℓ {l = l} T)    = ∀ℓ {l = Lren ρ l} {! TLren (Lliftᵣ ρ) T  !}

TTwk : Type Δ l′ → Type (l ∷ Δ) l′
TTwk = TTren (Twkᵣ Tidᵣ)

TLwk : Type Δ l′ → Type (∷l Δ) (Lwk l′)
TLwk T = {!  TLren (Lwkᵣ Lidᵣ) T !}

TSub : TEnv δ → TEnv δ → Set
TSub {δ} Δ₁ Δ₂ = ∀ μ (l : Lvl δ μ) → Δ₁ ∍ l → Type Δ₂ l

Tidₛ : TSub Δ Δ
Tidₛ _ _ = `_

Tdropₛ : TSub (l ∷ Δ₁) Δ₂ → TSub Δ₁ Δ₂
Tdropₛ σ _ _ x = σ _ _ (there x)

Twkₛ : TSub Δ₁ Δ₂ → TSub Δ₁ (l ∷ Δ₂)
Twkₛ σ _ _ x = TTwk (σ _ _ x)

TTliftₛ : TSub Δ₁ Δ₂ → ∀ (l : Lvl δ μ) → TSub (l ∷ Δ₁) (l ∷ Δ₂)  
TTliftₛ σ _ _ _ here = ` here
TTliftₛ σ _ _ _ (there x) = TTwk (σ _ _ x)

TLliftₛ : TSub Δ₁ Δ₂ → TSub (∷l Δ₁) (∷l Δ₂)  
TLliftₛ σ _ _ (lskip x) = TLwk (σ _ _ x)

Tsub : TSub Δ₁ Δ₂ → Type Δ₁ l → Type Δ₂ l
Tsub σ Nat       = Nat
Tsub σ (` x)     = σ _ _ x
Tsub σ (T₁ ⇒ T₂) = Tsub σ T₁ ⇒ Tsub σ T₂
Tsub σ (∀α T)    = ∀α (Tsub (TTliftₛ σ _) T)
Tsub σ (∀ℓ T)    = ∀ℓ (Tsub (TLliftₛ σ) T)

Δsub : LSub δ₁ δ₂ → TEnv δ₁ → TEnv δ₂
Δsub σ []      = []
Δsub σ (l ∷ Δ) = Lsub σ l ∷ Δsub σ Δ
Δsub σ (∷l Δ)  = Δsub (Ldropₛ σ) Δ

postulate 
  TLsub : {Δ₁ : TEnv δ₁} (σ : LSub δ₁ δ₂) → 
    Type Δ₁ l → Type (Δsub σ Δ₁) (Lsub σ l) 
    
Textₛ : TSub Δ₁ Δ₂ → Type Δ₂ l → TSub (l ∷ Δ₁) Δ₂
Textₛ σ T′ _ _ here = T′
Textₛ σ T′ _ _ (there x)   = σ _ _ x

_[_]TT : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
T [ T′ ]TT = Tsub (Textₛ Tidₛ T′) T

_[_]TL : ∀ {Δ : TEnv δ} {l : Lvl δ μ} →
    Type (∷l Δ) (Lwk l) → Lvl δ <ω → Type Δ l
T [ l′ ]TL = {! TLsub ? T  !}

_T≫ᵣᵣ_ : TRen Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TRen Δ₁ Δ₃
(ρ₁ T≫ᵣᵣ ρ₂) _ _ x = ρ₂ _ _ (ρ₁ _ _ x)

_T≫ᵣₛ_ : TRen Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(ρ T≫ᵣₛ σ) _ _ x = σ _ _ (ρ _ _ x)

_T≫ₛᵣ_ : TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ T≫ₛᵣ ρ) _ _ x = TTren ρ (σ _ _ x)

_T≫ₛₛ_ : TSub Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ₁ T≫ₛₛ σ₂) _ _ x = Tsub σ₂ (σ₁ _ _ x)
       
⟦_⟧Δ_ : (Δ : TEnv δ) → (κ : ⟦ δ ⟧δ) → Set (suc⨆Δ κ Δ)
⟦  []   ⟧Δ κ = ⊤
⟦ l ∷ Δ ⟧Δ κ = Set (⟦ l ⟧L κ) × ⟦ Δ ⟧Δ κ
⟦ ∷l Δ  ⟧Δ κ = ⟦ Δ ⟧Δ drop-κ κ
  
[]η : ∀ {δ} {κ : ⟦ δ ⟧δ} → ⟦ [] ⟧Δ κ
[]η = tt
  
_∷η_ : ∀ {l : Lvl δ μ} {Δ : TEnv δ} → Set (⟦ l ⟧L κ) → ⟦ Δ ⟧Δ κ → ⟦ l ∷ Δ ⟧Δ κ
_∷η_ = _,_

_∷ηℓ_ : {Δ : TEnv δ} → {κ : ⟦ δ ⟧δ} → 
  (ℓ : BoundLevel ⌊ ω ⌋) → ⟦ Δ ⟧Δ κ → ⟦ ∷l Δ ⟧Δ (ℓ ∷κ κ)
_∷ηℓ_ {δ} {Δ} {κ} ℓ η = η

lookup-η : ∀ {l : Lvl δ μ} {Δ : TEnv δ} → ⟦ Δ ⟧Δ κ → Δ ∍ l → Set (⟦ l ⟧L κ) 
lookup-η (A , _) here = A
lookup-η (_ , η) (there x) = lookup-η η x
lookup-η {κ = κ} η (lskip {l = l} x) = cast (sym (⟦Lwk⟧L-drop  l κ)) (lookup-η η x)

drop-η : ∀ {l : Lvl δ μ} {Δ : TEnv δ} → ⟦ l ∷ Δ ⟧Δ κ → ⟦ Δ ⟧Δ κ 
drop-η (_ , η) = η

⟦_⟧T : ∀ {l : Lvl δ μ} {Δ : TEnv δ} → 
  (T : Type Δ l) → (κ : ⟦ δ ⟧δ) → ⟦ Δ ⟧Δ κ → Set (⟦ l ⟧L κ)
⟦ Nat     ⟧T κ η = ℕ
⟦ ` α     ⟧T κ η = lookup-η η α
⟦ T₁ ⇒ T₂ ⟧T κ η = ⟦ T₁ ⟧T κ η → ⟦ T₂ ⟧T κ η   
⟦_⟧T {δ = δ} {Δ = Δ} (∀α {l = l} T) κ η = 
    ∀ (A : Set (⟦ l ⟧L κ)) → ⟦ T ⟧T κ (_∷η_ {κ = κ} {l = l} {Δ = Δ} A η)
⟦_⟧T {l = l} {Δ = Δ} (∀ℓ T) κ η = ∀ (ℓ : BoundLevel ⌊ ω ⌋) → 
  cast (⟦Lwk⟧L-∷κ l κ ℓ) (Lift ⌊ ω ⌋ (⟦ T ⟧T (ℓ ∷κ κ) (_∷ηℓ_ {Δ = Δ} {κ = κ} ℓ η)))

postulate 
 ⟦_⟧Tρ_ : ∀ {κ : ⟦ δ ⟧δ} {Δ₁ Δ₂ : TEnv δ} → TRen Δ₁ Δ₂ → ⟦ Δ₂ ⟧Δ κ → ⟦ Δ₁ ⟧Δ κ
 -- ⟦_⟧Tρ_ {κ = κ} {Δ₁ = []} ρ η = []η {κ = κ} 
 -- ⟦_⟧Tρ_ {δ = δ} {κ = κ} {Δ₁ = l ∷ Δ₁} ρ η = _∷η_ {l = l} {Δ = Δ₁} (⟦ ` ρ _ _ here ⟧T κ η) (⟦ TTdropᵣ ρ ⟧Tρ η)
-- ⟦_⟧Tρ_ {κ = ℓ , κ} {Δ₁ = ∷l Δ₁} {Δ₂} ρ η = _∷ηℓ_ {Δ = Δ₁} {κ = κ} ℓ {!   !}

postulate
  ⟦⟧ρ-wkᵣ : {κ : ⟦ δ ⟧δ} {Δ₁ Δ₂ : TEnv δ} (ρ : TRen Δ₁ Δ₂) (η : ⟦ Δ₂ ⟧Δ κ) (A : Set (⟦ l ⟧L κ)) → 
    (⟦ ρ T≫ᵣᵣ Twkᵣ Tidᵣ ⟧Tρ (A ∷η η)) ≡ ⟦ ρ ⟧Tρ η
-- ⟦⟧ρ-wkᵣ {[]} ρ η A    = refl
-- ⟦⟧ρ-wkᵣ {ℓ ∷ Δ} ρ η A = cong ((lookup-η η (ρ _ (here refl))) ,_) (⟦⟧ρ-wkᵣ (TTdropᵣ ρ) η A)
-- 
postulate
  ⟦⟧ρ-idᵣ : {κ : ⟦ δ ⟧δ} (η : ⟦ Δ ⟧Δ κ) → (⟦ Tidᵣ ⟧Tρ η) ≡ η
-- ⟦⟧ρ-idᵣ {[]}     η = refl
-- ⟦⟧ρ-idᵣ {x ∷ Δ₂} (A , γ) = cong (A ∷η_) (trans (⟦⟧ρ-wkᵣ Tidᵣ γ A) (⟦⟧ρ-idᵣ γ))
-- 
-- ⟦⟧ρ-liftᵣ : ∀ {ℓ} (ρ : TRen Δ₁ Δ₂) (η : ⟦ Δ₂ ⟧Δ) (A : Set ℓ) →
--    (⟦ Tliftᵣ ρ ℓ ⟧ρ (A ∷η η)) ≡ (A ∷η (⟦ ρ ⟧ρ η))
-- ⟦⟧ρ-liftᵣ ρ η A = cong (_ ∷η_) (⟦⟧ρ-wkᵣ ρ η A)
--   
postulate
  ⟦⟧T-ren : {l : Lvl δ μ} {κ : ⟦ δ ⟧δ} (η : ⟦ Δ₂ ⟧Δ κ) (ρ : TRen Δ₁ Δ₂) (T : Type Δ₁ l) → 
    ⟦ TTren ρ T ⟧T κ η ≡ ⟦ T ⟧T κ (⟦ ρ ⟧Tρ η)
-- ⟦⟧T-ren η ρ Nat       = refl
-- ⟦⟧T-ren η ρ (` x)     = ⟦⟧Δ-lookup η ρ x
--   where ⟦⟧Δ-lookup : ∀ {ℓ} (η : ⟦ Δ₂ ⟧Δ) (ρ : TRen Δ₁ Δ₂) (x : ℓ ∈ Δ₁) → 
--                         (⟦ ` ρ ℓ x ⟧T η) ≡ (⟦ ` x ⟧T (⟦ ρ ⟧ρ η))
--         ⟦⟧Δ-lookup η ρ (here refl) = refl
--         ⟦⟧Δ-lookup η ρ (there x) rewrite ⟦⟧Δ-lookup η (TTdropᵣ ρ) x = refl
-- ⟦⟧T-ren η ρ (T₁ ⇒ T₂) rewrite ⟦⟧T-ren η ρ T₁ | ⟦⟧T-ren η ρ T₂ = refl
-- ⟦⟧T-ren η ρ (∀α {ℓ} T) = dep-ext λ A → 
--   trans (⟦⟧T-ren (A ∷η η) (Tliftᵣ ρ ℓ) T) (cong (λ η → ⟦ T ⟧T (A , η)) (⟦⟧ρ-wkᵣ ρ η A))
--
postulate 
  ⟦_⟧Tσ_ : ∀ {Δ₁ Δ₂ : TEnv δ} {κ : ⟦ δ ⟧δ} → TSub Δ₁ Δ₂  → ⟦ Δ₂ ⟧Δ κ → ⟦ Δ₁ ⟧Δ κ
-- ⟦_⟧σ_ {Δ₁ = []}    σ η = []η
-- ⟦_⟧σ_ {Δ₁ = _ ∷ _} σ η = (⟦ σ _ (here refl) ⟧T η) ∷η (⟦ Tdropₛ σ ⟧σ η)
-- 
-- ⟦⟧σ-wkᵣ : (σ : TSub Δ₁ Δ₂) (η : ⟦ Δ₂ ⟧Δ) (A : Set ℓ) → 
--   (⟦ σ T≫ₛᵣ Twkᵣ Tidᵣ ⟧σ (A ∷η η)) ≡ ⟦ σ ⟧σ η
-- ⟦⟧σ-wkᵣ {[]} σ η A    = refl
-- ⟦⟧σ-wkᵣ {ℓ ∷ Δ} σ η A = 
--   cong₂ _∷η_ (trans (⟦⟧T-ren (A ∷η η) (Twkᵣ Tidᵣ) (σ ℓ (here refl))) 
--       (cong (λ η → ⟦ σ ℓ (here refl) ⟧T η) (trans (⟦⟧ρ-wkᵣ Tidᵣ η A) (⟦⟧ρ-idᵣ η)))) 
--   (⟦⟧σ-wkᵣ (Tdropₛ σ) η A)
postulate
  ⟦⟧σ-idₛ : ∀ {Δ : TEnv δ} {κ : ⟦ δ ⟧δ} (η : ⟦ Δ ⟧Δ κ) → (⟦ Tidₛ ⟧Tσ η) ≡ η
  
-- ⟦⟧σ-idₛ {[]}     η = refl
-- ⟦⟧σ-idₛ {x ∷ Δ₂} (A , γ) = cong (A ∷η_) (trans (⟦⟧σ-wkᵣ Tidₛ γ A) (⟦⟧σ-idₛ γ))
--
postulate 
  -- postulate
  -- ⟦⟧T-ren : {l : Lvl δ μ} {κ : ⟦ δ ⟧δ} (η : ⟦ Δ₂ ⟧Δ κ) (ρ : TRen Δ₁ Δ₂) (T : Type Δ₁ l) → 
  --   ⟦ TTren ρ T ⟧T κ η ≡ ⟦ T ⟧T κ (⟦ ρ ⟧Tρ η)
  ⟦⟧T-sub :  {l : Lvl δ μ} {κ : ⟦ δ ⟧δ} (η : ⟦ Δ₂ ⟧Δ κ) (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ l) → 
    ⟦ Tsub σ T ⟧T κ η ≡ ⟦ T ⟧T κ (⟦ σ ⟧Tσ η)
-- ⟦⟧T-sub η σ Nat       = refl
-- ⟦⟧T-sub η σ (` x)     = ⟦⟧Δ-lookup η σ x
--   where ⟦⟧Δ-lookup : ∀ {ℓ} (η : ⟦ Δ₂ ⟧Δ) (σ : TSub Δ₁ Δ₂) (x : ℓ ∈ Δ₁) → 
--                           (⟦ σ ℓ x ⟧T η) ≡ (⟦ ` x ⟧T (⟦ σ ⟧σ η))
--         ⟦⟧Δ-lookup η σ (here refl) = refl
--         ⟦⟧Δ-lookup η σ (there x) rewrite ⟦⟧Δ-lookup η (Tdropₛ σ) x = refl
-- ⟦⟧T-sub η σ (T₁ ⇒ T₂) rewrite ⟦⟧T-sub η σ T₁ | ⟦⟧T-sub η σ T₂ = refl
-- ⟦⟧T-sub η σ (∀α T)    = dep-ext λ A → 
--   trans (⟦⟧T-sub (A ∷η η) (Tliftₛ σ _) T) (cong (λ η → ⟦ T ⟧T (A , η)) (⟦⟧σ-wkᵣ σ η A))
--   
data EEnv : (Δ : TEnv δ) → Set where
  []   : EEnv Δ
  _∷_  : Type Δ l → EEnv Δ → EEnv Δ
  _∷l_ : (l : Lvl δ μ) → EEnv Δ → EEnv (l ∷ Δ)
  ∷l_ : EEnv Δ → EEnv (∷l Δ)

variable
  Γ Γ′ Γ₁ Γ₂ Γ₃ : EEnv Δ

data _∋_ : EEnv Δ → Type Δ l → Set where
  here  : (T ∷ Γ) ∋ T
  there : Γ ∋ T → (T′ ∷ Γ) ∋ T
  tskip : Γ ∋ T → (l ∷l Γ) ∋ TTwk T
  lskip : Γ ∋ T → (∷l Γ) ∋ TLwk T

⨆Γ : ∀ {Δ : TEnv δ} → EEnv Δ → ⟦ δ ⟧δ → Level
⨆Γ []                κ = zero 
⨆Γ (_∷_ {l = l} T Γ) κ = ⟦ l ⟧L κ  ⊔ ⨆Γ Γ κ 
⨆Γ (ℓ ∷l Γ)          κ = ⨆Γ Γ κ
⨆Γ (∷l Γ)            κ = ⨆Γ Γ (drop-κ κ)

data Expr {Δ : TEnv δ} (Γ : EEnv Δ) : Type Δ l → Set where
  `_    : Γ ∋ T → Expr Γ T
  #_    : ℕ → Expr Γ Nat
  ‵suc  : Expr Γ Nat → Expr Γ Nat
  λx_   : Expr (T ∷ Γ) T′ → Expr Γ (T ⇒ T′)
  Λ_⇒_  : ∀ l {T : Type (l ∷ Δ) l′} → Expr (l ∷l Γ) T → Expr Γ (∀α T)
  Λℓ_⇒_ : ∀ (l : Lvl δ μ) {T : Type (∷l Δ) (Lwk l)} → Expr (∷l Γ) T → Expr Γ (∀ℓ T)
  _·_   : Expr Γ (T ⇒ T′) → Expr Γ T → Expr Γ T′
  _∙_   : Expr Γ (∀α T) → (T′ : Type Δ l) → Expr Γ (T [ T′ ]TT) 
  _∙ℓ_  : ∀ {l : Lvl δ μ} {T : Type (∷l Δ) (Lwk l)} → Expr Γ (∀ℓ T) → (l′ : Lvl δ <ω) → Expr Γ (T [ l′ ]TL) 

⟦_⟧Γ   : ∀ {δ} {Δ : TEnv δ} → (Γ : EEnv Δ) → (κ : ⟦ δ ⟧δ) → ⟦ Δ ⟧Δ κ → Set (⨆Γ Γ κ)
⟦ []     ⟧Γ κ η = ⊤
⟦ T ∷ Γ  ⟧Γ κ η = ⟦ T ⟧T κ η × ⟦ Γ ⟧Γ κ η
⟦_⟧Γ {Δ = l ∷ Δ} (l ∷l Γ) κ η = ⟦ Γ ⟧Γ κ (drop-η {κ = κ} {l = l} {Δ = Δ} η) 
⟦ ∷l Γ   ⟧Γ κ η = ⟦ Γ ⟧Γ (drop-κ κ) η 

[]γ : ∀ {Δ : TEnv δ} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → ⟦_⟧Γ {Δ = Δ} [] κ η
[]γ = tt
   
_∷γ_   : ∀ {l : Lvl δ μ} {Δ : TEnv δ} {T : Type Δ l} {Γ : EEnv Δ} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ T ⟧T κ η → ⟦ Γ ⟧Γ κ η → ⟦ T ∷ Γ ⟧Γ κ η
_∷γ_ = _,_
    
_∷γl_   : ∀ {l : Lvl δ μ} {Δ : TEnv δ} {Γ : EEnv Δ} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → 
    (A : Set (⟦ l ⟧L κ)) → ⟦ Γ ⟧Γ κ η → ⟦ l ∷l Γ ⟧Γ κ (_∷η_ {κ = κ} {l = l} {Δ = Δ} A η)
_∷γl_ {Γ = Γ} A γ = γ

_∷γℓ_   : ∀ {l : Lvl δ μ} {Δ : TEnv δ} {Γ : EEnv Δ} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → 
    (ℓ : BoundLevel ⌊ ω ⌋) → ⟦ Γ ⟧Γ κ η → ⟦ ∷l Γ ⟧Γ (ℓ ∷κ κ) (_∷ηℓ_ {Δ = Δ} {κ = κ} ℓ η)
_∷γℓ_ {Γ = Γ} A γ = γ


lookup-γ : ∀ {l : Lvl δ μ} {Δ : TEnv δ} {Γ : EEnv Δ} {T : Type Δ l} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ Γ ⟧Γ κ η → Γ ∋ T → ⟦ T ⟧T κ η 
lookup-γ (A , γ) here       = A
lookup-γ (_ , γ) (there x)  = lookup-γ γ x
lookup-γ {κ = κ} {Γ = _ ∷l Γ} {η = η} γ (tskip {T = T} x) = subst id (sym (⟦⟧T-ren η (Twkᵣ Tidᵣ) T)) 
   (lookup-γ (subst (λ η → ⟦ Γ ⟧Γ κ η) (sym (trans (⟦⟧ρ-wkᵣ Tidᵣ (proj₂ η) (proj₁ η)) (⟦⟧ρ-idᵣ (proj₂ η)))) γ) x) 
lookup-γ {κ = κ} {Γ = ∷l Γ} {η = η} γ (lskip x) = lookup-γ {κ = drop-κ κ} γ x
  -- subst id (sym (⟦⟧T-ren η (Twkᵣ Tidᵣ) T)) 
  -- (lookup-γ (subst (λ η → ⟦ Γ ⟧Γ η) (sym (trans (⟦⟧ρ-wkᵣ Tidᵣ (proj₂ η) (proj₁ η)) (⟦⟧ρ-idᵣ (proj₂ η)))) γ) x) 
  
⟦_⟧E : {l : Lvl δ μ} {Δ : TEnv δ} {T : Type Δ l} {Γ : EEnv Δ} → 
  Expr Γ T →  (κ : ⟦ δ ⟧δ) (η : ⟦ Δ ⟧Δ κ) → ⟦ Γ ⟧Γ κ η → ⟦ T ⟧T κ η
⟦ ` x     ⟧E κ η γ = {!   !}
⟦ # n     ⟧E κ η γ = n
⟦ ‵suc e  ⟧E κ η γ = sucℕ (⟦ e ⟧E κ η γ)
⟦_⟧E {Δ = Δ} {T = (T₁ ⇒ T₂)} {Γ} (λx e) κ η γ = λ x → ⟦ e ⟧E κ η (_∷γ_ {T = T₁} {Γ = Γ} x γ)
⟦_⟧E {Δ = Δ} {T = T} {Γ = Γ} (Λ_⇒_ {l′ = l′} l e) κ η γ = λ A → ⟦ e ⟧E κ (_∷η_ {κ = κ} {l = l} {Δ = Δ}A η) (_∷γl_ {l = l} {Γ = Γ} A γ)
⟦_⟧E {_} {Δ} {T} {Γ = Γ} (Λℓ l ⇒ e) κ η γ =  λ ℓ → {! lift (⟦ e ⟧E (ℓ ∷κ κ) (ℓ ∷ηℓ η) (ℓ ∷γℓ γ))  !}
⟦ e₁ · e₂ ⟧E κ η γ = ⟦ e₁ ⟧E κ η γ (⟦ e₂ ⟧E κ η γ)
⟦ _∙_ {T = T} e T′ ⟧E κ η γ = subst id (trans 
  (cong (λ η′ → ⟦ T ⟧T κ ((⟦ T′ ⟧T κ η) , η′)) (sym (⟦⟧σ-idₛ η))) 
  (sym {! (⟦⟧T-sub η (Textₛ Tidₛ T′) T)  !})) (⟦ e ⟧E κ η γ (⟦ T′ ⟧T κ η)) 
⟦ _∙ℓ_ {l = l} e l′ ⟧E κ η γ = ⟦ e ⟧E κ η γ (⟦ l′ ⟧L′ κ) 
   
                         