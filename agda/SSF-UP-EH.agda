module SSF-UP-EH where

open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open import Level using (Level; Lift; lift; zero; suc; _⊔_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ) 
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_) 
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; icong; subst)
open import Function using (_∘_; id; flip; _$_)
open import ExtendedHierarchy using (𝟎; 𝟏; ω; ω²; ⌊_⌋; cast; cast-push; cast-pop; β-suc-zero; β-suc-ω; β-suc-⌊⌋; ω^_+_;  <₁; <₂; <₃)
open import BoundQuantification using (BoundLevel; BoundLift; bound-lift; bound-unlift; _,_; #; #<Λ; _<_; _≤_; ≤-id; ≤-suc; ≤-add; ≤-exp; ≤-lublub; <-suc-lim; lim)

LEnv = List ⊤

variable
  δ δ′ δ₁ δ₂ δ₃ : LEnv

data LivesIn : Set where
  <ω : LivesIn
  <ω> : LivesIn

variable
  μ μ′ μ₁ μ₂ μ₃ : LivesIn
    
data Lvl (δ : LEnv) : LivesIn → Set where 
  `zero : Lvl δ <ω
  `suc  : Lvl δ μ → Lvl δ μ
  `_    : tt ∈ δ → Lvl δ <ω
  _`⊔_  : Lvl δ μ → Lvl δ μ → Lvl δ μ
  ⟨_⟩   : Lvl δ μ → Lvl δ <ω>
  `ω    : Lvl δ <ω>
      
variable
  l l′ l₁ l₂ l₃ : Lvl δ μ

postulate 
  Lwk  : Lvl δ μ → Lvl (tt ∷ δ) μ

postulate
  _[_]LL : Lvl (tt ∷ δ) μ → Lvl δ <ω → Lvl δ μ

⟦_⟧δ : (δ : LEnv) → Set
⟦ []    ⟧δ = ⊤
⟦ x ∷ δ ⟧δ = BoundLevel ⌊ ω ⌋ × ⟦ δ ⟧δ
    
_∷κ_ : BoundLevel ⌊ ω ⌋ → ⟦ δ ⟧δ → ⟦ tt ∷ δ ⟧δ
_∷κ_ = _,_

lookup-κ : ⟦ δ ⟧δ → tt ∈ δ → BoundLevel ⌊ ω ⌋
lookup-κ {_ ∷ δ} (ℓ , κ) (here refl) = ℓ
lookup-κ {_ ∷ δ} (ℓ , κ) (there x)   = lookup-κ κ x

drop-κ : ⟦ tt ∷ δ ⟧δ → ⟦ δ ⟧δ
drop-κ (_ , κ) = κ

⟦_⟧L : ∀ {δ : LEnv} → (l : Lvl δ μ) → ⟦ δ ⟧δ → Level
⟦ `zero     ⟧L κ = zero
⟦ `suc l    ⟧L κ = suc (⟦ l ⟧L κ)
⟦ ` x       ⟧L κ = # (lookup-κ κ x)
⟦ l₁ `⊔ l₂  ⟧L κ = (⟦ l₁ ⟧L κ) ⊔ (⟦ l₂ ⟧L κ)
⟦ ⟨ l ⟩     ⟧L κ = ⟦ l ⟧L κ
⟦ `ω        ⟧L κ = ⌊ ω ⌋

⟦_⟧L′ : ∀ {δ : LEnv} → Lvl δ <ω → ⟦ δ ⟧δ → BoundLevel ⌊ ω ⌋
⟦ `zero    ⟧L′ κ = zero , ≤-exp zero (subst (suc zero ≤_) β-suc-zero (≤-id (suc zero)))
⟦ `suc l   ⟧L′ κ = (suc (# (⟦ l ⟧L′ κ))) , <-suc-lim _ _ (#<Λ (⟦ l ⟧L′ κ)) (lim (ω^ zero + zero) (subst (suc zero ≤_) β-suc-zero (≤-id (suc zero))))
⟦ ` x      ⟧L′ κ = lookup-κ κ x 
⟦ l₁ `⊔ l₂ ⟧L′ κ = # (⟦ l₁ ⟧L′ κ) ⊔ # (⟦ l₂ ⟧L′ κ) , ≤-lublub (#<Λ (⟦ l₁ ⟧L′ κ)) (#<Λ (⟦ l₂ ⟧L′ κ))

postulate
  ⟦⟧L-Lwk-dropκ : ∀ (l : Lvl δ μ) (κ : ⟦ tt ∷ δ ⟧δ) → ⟦ l ⟧L (drop-κ κ) ≡ ⟦ Lwk l ⟧L κ 
  ⟦⟧L-Lwk-∷κ :  ∀ (l : Lvl δ μ) (κ : ⟦ δ ⟧δ) ℓ → ⟦ Lwk l ⟧L (ℓ ∷κ κ) ≡ ⟦ l ⟧L κ
  ⟦⟧L-Lwk-[]LL :  ∀ (l : Lvl δ μ) (κ : ⟦ δ ⟧δ) l′ → ⟦ Lwk l [ l′ ]LL ⟧L κ ≡ ⟦ Lwk l ⟧L (⟦ l′ ⟧L′ κ , κ)

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
  ∀α    : {l : Lvl δ μ} → Type (l ∷ Δ) l′ → Type Δ (`suc l `⊔ l′) 
  ∀ℓ    : {l : Lvl δ μ} → Type (∷l Δ) (Lwk l) → Type Δ (`ω `⊔ ⟨ l ⟩)
      
variable
  T T′ T₁ T₂ T₃ : Type Δ l

postulate
  TTwk : Type Δ l′ → Type (l ∷ Δ) l′

postulate
  TLwk : Type Δ l → Type (∷l Δ) (Lwk l)

postulate
  _[_]TT : Type (l ∷ Δ) l′ → Type Δ l → Type Δ l′
  _[_]TL : ∀ {Δ : TEnv δ} {l : Lvl (tt ∷ δ) μ} →
    Type (∷l Δ) l → (l′ : Lvl δ <ω) → Type Δ (l [ l′ ]LL)
       
⟦_⟧Δ_ : (Δ : TEnv δ) → (κ : ⟦ δ ⟧δ) → Set (suc⨆Δ κ Δ)
⟦  []   ⟧Δ κ = ⊤
⟦ l ∷ Δ ⟧Δ κ = Set (⟦ l ⟧L κ) × ⟦ Δ ⟧Δ κ
⟦ ∷l Δ  ⟧Δ κ = ⟦ Δ ⟧Δ drop-κ κ

[]η : ∀ {δ} {κ : ⟦ δ ⟧δ} → ⟦ [] ⟧Δ κ
[]η = tt
  
_∷η_ : ∀ {l : Lvl δ μ} {Δ : TEnv δ} {κ : ⟦ δ ⟧δ} → Set (⟦ l ⟧L κ) → ⟦ Δ ⟧Δ κ → ⟦ l ∷ Δ ⟧Δ κ
_∷η_ = _,_

lookup-η : ∀ {l : Lvl δ μ} {Δ : TEnv δ} {κ : ⟦ δ ⟧δ} → ⟦ Δ ⟧Δ κ → Δ ∍ l → Set (⟦ l ⟧L κ) 
lookup-η (A , _) here                = A
lookup-η (_ , η) (there x)           = lookup-η η x
lookup-η {κ = κ} η (lskip {l = l} x) = cast (⟦⟧L-Lwk-dropκ l κ) (lookup-η η x)

drop-η : ∀ {l : Lvl δ μ} {Δ : TEnv δ} {κ : ⟦ δ ⟧δ} → ⟦ l ∷ Δ ⟧Δ κ → ⟦ Δ ⟧Δ κ 
drop-η (_ , η) = η

⟦_⟧T : ∀ {l : Lvl δ μ} {Δ : TEnv δ} → 
  (T : Type Δ l) → (κ : ⟦ δ ⟧δ) → ⟦ Δ ⟧Δ κ → Set (⟦ l ⟧L κ)
⟦ Nat     ⟧T κ η = ℕ
⟦ ` α     ⟧T κ η = lookup-η η α
⟦ T₁ ⇒ T₂ ⟧T κ η = ⟦ T₁ ⟧T κ η → ⟦ T₂ ⟧T κ η   
⟦_⟧T {δ = δ} {Δ = Δ} (∀α {l = l} T) κ η = 
    ∀ (A : Set (⟦ l ⟧L κ)) → ⟦ T ⟧T κ (_∷η_ {l = l} {Δ = Δ} {κ = κ}  A η)
⟦_⟧T {l = l} {Δ = Δ} (∀ℓ {l = l₁} T) κ η = ∀ (ℓ : BoundLevel ⌊ ω ⌋) → 
  cast (cong (⌊ ω ⌋ ⊔_) (⟦⟧L-Lwk-∷κ l₁ κ ℓ)) (Lift ⌊ ω ⌋ (⟦ T ⟧T (ℓ ∷κ κ) η))

postulate
  ⟦⟧T-TLwk-∷κ : ∀ {l : Lvl δ μ} {Δ : TEnv δ} {ℓ} (T : Type Δ l) → (κ : ⟦ δ ⟧δ) → (η : ⟦ Δ ⟧Δ κ) →
    ⟦ T ⟧T κ η ≡ cast (⟦⟧L-Lwk-∷κ l κ ℓ) (⟦ TLwk T ⟧T (ℓ , κ) η) 
  ⟦⟧T-TTwk-∷η : ∀ {l : Lvl δ μ} {l′ : Lvl δ μ′} {Δ : TEnv δ} (T : Type Δ l) → (κ : ⟦ δ ⟧δ) {A : Set (⟦ l′ ⟧L κ)} → (η : ⟦ Δ ⟧Δ κ) → 
    ⟦ T ⟧T κ η ≡ ⟦ TTwk {l = l′} T ⟧T κ (A , η)

  ⟦⟧T-[]LT-∷κ : ∀ {l : Lvl δ μ} (T : Type (∷l Δ) (Lwk l)) (l′ : Lvl δ <ω) (κ : ⟦ δ ⟧δ) → (η : ⟦ Δ ⟧Δ κ) →  
    ⟦ T ⟧T (⟦ l′ ⟧L′ κ , κ) η ≡ cast (⟦⟧L-Lwk-[]LL l κ l′) (⟦ T [ l′ ]TL ⟧T κ η)
  ⟦⟧T-[]TT-∷η : ∀ {l : Lvl δ μ} {l′ : Lvl δ μ′} (T : Type (l′ ∷ Δ) l) (T′ : Type Δ l′) (κ : ⟦ δ ⟧δ) → (η : ⟦ Δ ⟧Δ κ) → 
    ⟦ T ⟧T κ (_∷η_ {l = l′} {Δ = Δ} {κ = κ} (⟦ T′ ⟧T κ η) η) ≡ ⟦ T [ T′ ]TT ⟧T κ η
    
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
  Λℓ_   : ∀ {l : Lvl δ μ} {T : Type (∷l Δ) (Lwk l)} → Expr (∷l Γ) T → Expr Γ (∀ℓ T)
  _·_   : Expr Γ (T ⇒ T′) → Expr Γ T → Expr Γ T′
  _∙_   : Expr Γ (∀α T) → (T′ : Type Δ l) → Expr Γ (T [ T′ ]TT) 
  _∙ℓ_  : ∀ {l : Lvl δ μ} {T : Type (∷l Δ) (Lwk l)} → Expr Γ (∀ℓ T) → (l′ : Lvl δ <ω) → Expr Γ (T [ l′ ]TL) 

⟦_⟧Γ   : ∀ {δ} {Δ : TEnv δ} → (Γ : EEnv Δ) → (κ : ⟦ δ ⟧δ) → ⟦ Δ ⟧Δ κ → Set (⨆Γ Γ κ)
⟦ []     ⟧Γ κ η = ⊤
⟦ T ∷ Γ  ⟧Γ κ η = ⟦ T ⟧T κ η × ⟦ Γ ⟧Γ κ η
⟦_⟧Γ {Δ = l ∷ Δ} (l ∷l Γ) κ η = ⟦ Γ ⟧Γ κ (drop-η {l = l} {Δ = Δ} {κ = κ} η) 
⟦ ∷l Γ   ⟧Γ κ η = ⟦ Γ ⟧Γ (drop-κ κ) η 

[]γ : ∀ {Δ : TEnv δ} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → ⟦_⟧Γ {Δ = Δ} [] κ η
[]γ = tt
   
_∷γ_   : ∀ {l : Lvl δ μ} {Δ : TEnv δ} {T : Type Δ l} {Γ : EEnv Δ} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ T ⟧T κ η → ⟦ Γ ⟧Γ κ η → ⟦ T ∷ Γ ⟧Γ κ η
_∷γ_ = _,_

lookup-γ : ∀ {l : Lvl δ μ} {Δ : TEnv δ} {Γ : EEnv Δ} {T : Type Δ l} {κ : ⟦ δ ⟧δ} {η : ⟦ Δ ⟧Δ κ} → 
    ⟦ Γ ⟧Γ κ η → Γ ∋ T → ⟦ T ⟧T κ η 
lookup-γ (A , γ) here       = A
lookup-γ (_ , γ) (there x)  = lookup-γ γ x
lookup-γ {Γ = _ ∷l Γ} {κ = κ} {η = A , η} γ (tskip {T = T} x) = subst id (⟦⟧T-TTwk-∷η _ _ _) (lookup-γ γ x)
lookup-γ {δ = tt ∷ δ} {Γ = ∷l Γ} {κ = A , κ} {η = η} γ (lskip x) = cast-pop _ (subst id (⟦⟧T-TLwk-∷κ _ _ _) (lookup-γ {δ = δ} {κ = κ} γ x))

⟦_⟧E : {l : Lvl δ μ} {Δ : TEnv δ} {T : Type Δ l} {Γ : EEnv Δ} → 
  Expr Γ T → (κ : ⟦ δ ⟧δ) (η : ⟦ Δ ⟧Δ κ) → ⟦ Γ ⟧Γ κ η → ⟦ T ⟧T κ η
⟦ ` x     ⟧E κ η γ = lookup-γ γ x
⟦ # n     ⟧E κ η γ = n
⟦ ‵suc e  ⟧E κ η γ = sucℕ (⟦ e ⟧E κ η γ)
⟦_⟧E {Δ = Δ} {T = (T₁ ⇒ T₂)} {Γ} (λx e) κ η γ = λ x → ⟦ e ⟧E κ η (_∷γ_ {T = T₁} {Γ = Γ} x γ)
⟦_⟧E {Δ = Δ} {T = T} {Γ = Γ} (Λ_⇒_ {l′ = l′} l e) κ η γ = λ A → ⟦ e ⟧E κ (_∷η_ {l = l} {Δ = Δ} {κ = κ} A η) γ
⟦_⟧E {l = `ω `⊔ ⟨ l₁ ⟩} {T = ∀ℓ T} (Λℓ e) κ η γ = 
  λ (ℓ : BoundLevel ⌊ ω ⌋) → cast-push _ (lift {ℓ = ⌊ ω ⌋} (⟦ e ⟧E (ℓ ∷κ κ) η γ))
⟦ e₁ · e₂ ⟧E κ η γ = ⟦ e₁ ⟧E κ η γ (⟦ e₂ ⟧E κ η γ)
⟦_⟧E {Δ = Δ} (_∙_ {T = T} e T′) κ η γ = subst id (⟦⟧T-[]TT-∷η _ _ _ _) (⟦ e ⟧E κ η γ (⟦ T′ ⟧T κ η)) 
⟦ _∙ℓ_ {l = l} e l′ ⟧E κ η γ = cast-pop _ (subst id (⟦⟧T-[]LT-∷κ _ _ _ _) 
  (Lift.lower (cast-pop (cong (_⊔_ (ω^ ω^ zero + zero + zero)) (⟦⟧L-Lwk-∷κ l κ (⟦ l′ ⟧L′ κ))) (⟦ e ⟧E κ η γ (⟦ l′ ⟧L′ κ)))))
      
                               