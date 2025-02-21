module SSF where

open import Axiom.Extensionality.Propositional using (∀-extensionality; Extensionality)
open import Level using (Level; zero; suc; _⊔_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ) renaming (zero to zeroℕ; suc to sucℕ) 
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_) 
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Function using (_∘_; id; flip; _$_)

variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ : Level

postulate
  fun-ext : Extensionality ℓ₁ ℓ₂

dep-ext : {A : Set ℓ₁} {F G : (a : A) → Set ℓ₂} → 
  ((a : A) → F a ≡ G a) → ((a : A) → F a) ≡ ((a : A) → G a) 
dep-ext = ∀-extensionality fun-ext _ _

TEnv = List Level

variable
  Δ Δ′ Δ₁ Δ₂ Δ₃ : TEnv

suc⨆Δ_ : TEnv → Level
suc⨆Δ []       = zero
suc⨆Δ (ℓ ∷ ℓs) = suc ℓ ⊔ suc⨆Δ ℓs
   
data Type (Δ : TEnv) : Level → Set where
  Nat : Type Δ zero
  `_  : ℓ ∈ Δ → Type Δ ℓ
  _⇒_ : Type Δ ℓ₁ → Type Δ ℓ₂ → Type Δ (ℓ₁ ⊔ ℓ₂)
  ∀α  : Type (ℓ ∷ Δ) ℓ′ → Type Δ (suc ℓ ⊔ ℓ′)

variable
  T T′ T₁ T₂ T₃ : Type Δ ℓ

TRen : TEnv → TEnv → Set
TRen Δ₁ Δ₂ = ∀ ℓ → ℓ ∈ Δ₁ → ℓ ∈ Δ₂

variable 
  ρ ρ′ ρ₁ ρ₂ ρ₃ : TRen Δ₁ Δ₂

Tidᵣ : TRen Δ Δ
Tidᵣ _ = id

Tdropᵣ : TRen (ℓ ∷ Δ₁) Δ₂ → TRen Δ₁ Δ₂
Tdropᵣ ρ _ x = ρ _ (there x)

Twkᵣ : TRen Δ₁ Δ₂ → TRen Δ₁ (ℓ ∷ Δ₂)
Twkᵣ ρ _ x = there (ρ _ x)

Tliftᵣ : TRen Δ₁ Δ₂ → ∀ ℓ → TRen (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)
Tliftᵣ ρ _ _ (here refl) = here refl
Tliftᵣ ρ _ _ (there x)   = there (ρ _ x)

Tren : TRen Δ₁ Δ₂ → Type Δ₁ ℓ → Type Δ₂ ℓ
Tren ρ Nat       = Nat
Tren ρ (` x)     = ` ρ _ x
Tren ρ (T₁ ⇒ T₂) = Tren ρ T₁ ⇒ Tren ρ T₂
Tren ρ (∀α T)    = ∀α (Tren (Tliftᵣ ρ _) T)

Twk : Type Δ ℓ′ → Type (ℓ ∷ Δ) ℓ′
Twk = Tren (Twkᵣ Tidᵣ)

TSub : TEnv → TEnv → Set
TSub Δ₁ Δ₂ = ∀ ℓ → ℓ ∈ Δ₁ → Type Δ₂ ℓ

Tidₛ : TSub Δ Δ
Tidₛ _ = `_

Tdropₛ : TSub (ℓ ∷ Δ₁) Δ₂ → TSub Δ₁ Δ₂
Tdropₛ σ _ x = σ _ (there x)

Twkₛ : TSub Δ₁ Δ₂ → TSub Δ₁ (ℓ ∷ Δ₂)
Twkₛ σ _ x = Twk (σ _ x)

Tliftₛ : TSub Δ₁ Δ₂ → ∀ ℓ → TSub (ℓ ∷ Δ₁) (ℓ ∷ Δ₂)  
Tliftₛ σ _ _ (here refl) = ` (here refl)
Tliftₛ σ _ _ (there x)   = Twk (σ _ x)

Tsub : TSub Δ₁ Δ₂ → Type Δ₁ ℓ → Type Δ₂ ℓ
Tsub σ Nat       = Nat
Tsub σ (` x)     = σ _ x
Tsub σ (T₁ ⇒ T₂) = Tsub σ T₁ ⇒ Tsub σ T₂
Tsub σ (∀α T)    = ∀α (Tsub (Tliftₛ σ _) T)

Textₛ : TSub Δ₁ Δ₂ → Type Δ₂ ℓ → TSub (ℓ ∷ Δ₁) Δ₂
Textₛ σ T′ _ (here refl) = T′
Textₛ σ T′ _ (there x)   = σ _ x

_[_]T : Type (ℓ ∷ Δ) ℓ′ → Type Δ ℓ → Type Δ ℓ′
_[_]T T T′ = Tsub (Textₛ Tidₛ T′) T
    
_T≫ᵣᵣ_ : TRen Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TRen Δ₁ Δ₃
(ρ₁ T≫ᵣᵣ ρ₂) _ x = ρ₂ _ (ρ₁ _ x)

_T≫ᵣₛ_ : TRen Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(ρ T≫ᵣₛ σ) _ x = σ _ (ρ _ x)

_T≫ₛᵣ_ : TSub Δ₁ Δ₂ → TRen Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ T≫ₛᵣ ρ) _ x = Tren ρ (σ _ x)

_T≫ₛₛ_ : TSub Δ₁ Δ₂ → TSub Δ₂ Δ₃ → TSub Δ₁ Δ₃
(σ₁ T≫ₛₛ σ₂) _ x = Tsub σ₂ (σ₁ _ x)

module FunctionTypeSemEnv where
  -- example of using BoundQuantification to encode semantic environments as function that do not hit Setω
  open import BoundQuantification 
  
  ℓ∈Δ⇒ℓ<⨆Δ : ∀ {ℓ} {Δ : TEnv} → ℓ ∈ Δ → ℓ < (suc⨆Δ Δ)
  ℓ∈Δ⇒ℓ<⨆Δ {Δ = ℓ ∷ Δ}  (here refl) = ≤-lub (suc⨆Δ Δ) (≤-id (suc ℓ)) 
  ℓ∈Δ⇒ℓ<⨆Δ {Δ = ℓ′ ∷ Δ} (there x)   = ≤-lub (suc⨆Δ (ℓ′ ∷ Δ)) (ℓ∈Δ⇒ℓ<⨆Δ x) 
  
  ⟦_⟧Δ : (Δ : TEnv) → Set (suc⨆Δ Δ)
  ⟦ Δ ⟧Δ = ∀ (ℓ : BoundLevel (suc⨆Δ Δ)) → # ℓ ∈ Δ → BoundLift (#<Λ ℓ) (Set (# ℓ))
        
⟦_⟧Δ : (Δ : TEnv) → Set (suc⨆Δ Δ)
⟦  []   ⟧Δ = ⊤
⟦ ℓ ∷ Δ ⟧Δ = Set ℓ × ⟦ Δ ⟧Δ

variable 
   η η′ η₁ η₂ η₃ : ⟦ Δ ⟧Δ

[]η : ⟦ [] ⟧Δ
[]η = _
  
_∷η_ : Set ℓ → ⟦ Δ ⟧Δ → ⟦ ℓ ∷ Δ ⟧Δ
_∷η_ = _,_
  
lookup-η : ⟦ Δ ⟧Δ → ℓ ∈ Δ → Set ℓ 
lookup-η (A , _) (here refl) = A
lookup-η (_ , η) (there x)   = lookup-η η x

drop-η : ⟦ ℓ ∷ Δ ⟧Δ →  ⟦ Δ ⟧Δ
drop-η (_ , η) = η

⟦_⟧T_ : (T : Type Δ ℓ) → ⟦ Δ ⟧Δ → Set ℓ
⟦ Nat     ⟧T η = ℕ
⟦ ` x     ⟧T η = lookup-η η x
⟦ T₁ ⇒ T₂ ⟧T η = ⟦ T₁ ⟧T η → ⟦ T₂ ⟧T η   
⟦ ∀α T    ⟧T η = ∀ A → ⟦ T ⟧T (A ∷η η)  

⟦_⟧ρ_ : TRen Δ₁ Δ₂ → ⟦ Δ₂ ⟧Δ → ⟦ Δ₁ ⟧Δ
⟦_⟧ρ_ {Δ₁ = []}    ρ η = []η
⟦_⟧ρ_ {Δ₁ = _ ∷ _} ρ η = (⟦ ` ρ _ (here refl) ⟧T η) ∷η (⟦ Tdropᵣ ρ ⟧ρ η)

⟦Twkᵣ⟧ρ : (ρ : TRen Δ₁ Δ₂) (η : ⟦ Δ₂ ⟧Δ) (A : Set ℓ) → 
  (⟦ ρ T≫ᵣᵣ Twkᵣ Tidᵣ ⟧ρ (A ∷η η)) ≡ ⟦ ρ ⟧ρ η
⟦Twkᵣ⟧ρ {[]} ρ η A    = refl
⟦Twkᵣ⟧ρ {ℓ ∷ Δ} ρ η A = cong ((lookup-η η (ρ _ (here refl))) ,_) (⟦Twkᵣ⟧ρ (Tdropᵣ ρ) η A)

⟦⟧ρ-Tidᵣ : (η : ⟦ Δ ⟧Δ) → (⟦ Tidᵣ ⟧ρ η) ≡ η
⟦⟧ρ-Tidᵣ {[]}     η = refl
⟦⟧ρ-Tidᵣ {_ ∷ Δ₂} (A , η) = cong (A ∷η_) (trans (⟦Twkᵣ⟧ρ Tidᵣ η A) (⟦⟧ρ-Tidᵣ η))

⟦Tliftᵣ⟧ρ : ∀ (ρ : TRen Δ₁ Δ₂) (η : ⟦ Δ₂ ⟧Δ) (A : Set ℓ) →
   (⟦ Tliftᵣ ρ ℓ ⟧ρ (A ∷η η)) ≡ (A ∷η (⟦ ρ ⟧ρ η))
⟦Tliftᵣ⟧ρ ρ η A = cong (_ ∷η_) (⟦Twkᵣ⟧ρ ρ η A)
  
⟦Tren⟧T : (η : ⟦ Δ₂ ⟧Δ) (ρ : TRen Δ₁ Δ₂) (T : Type Δ₁ ℓ) → 
  ⟦ Tren ρ T ⟧T η ≡ ⟦ T ⟧T (⟦ ρ ⟧ρ η)
⟦Tren⟧T η ρ Nat       = refl
⟦Tren⟧T η ρ (` x)     = ⟦⟧Δ-lookup η ρ x
  where ⟦⟧Δ-lookup : ∀ {ℓ} (η : ⟦ Δ₂ ⟧Δ) (ρ : TRen Δ₁ Δ₂) (x : ℓ ∈ Δ₁) → 
                        (⟦ ` ρ ℓ x ⟧T η) ≡ (⟦ ` x ⟧T (⟦ ρ ⟧ρ η))
        ⟦⟧Δ-lookup η ρ (here refl) = refl
        ⟦⟧Δ-lookup η ρ (there x) rewrite ⟦⟧Δ-lookup η (Tdropᵣ ρ) x = refl
⟦Tren⟧T η ρ (T₁ ⇒ T₂) rewrite ⟦Tren⟧T η ρ T₁ | ⟦Tren⟧T η ρ T₂ = refl
⟦Tren⟧T η ρ (∀α {ℓ} T) = dep-ext λ A → 
  trans (⟦Tren⟧T (A ∷η η) (Tliftᵣ ρ ℓ) T) (cong (λ η → ⟦ T ⟧T (A , η)) (⟦Twkᵣ⟧ρ ρ η A))

⟦_⟧σ_ : TSub Δ₁ Δ₂ → ⟦ Δ₂ ⟧Δ → ⟦ Δ₁ ⟧Δ
⟦_⟧σ_ {Δ₁ = []}    σ η = []η
⟦_⟧σ_ {Δ₁ = _ ∷ _} σ η = (⟦ σ _ (here refl) ⟧T η) ∷η (⟦ Tdropₛ σ ⟧σ η)

⟦Twkᵣ⟧σ : (σ : TSub Δ₁ Δ₂) (η : ⟦ Δ₂ ⟧Δ) (A : Set ℓ) → 
  (⟦ σ T≫ₛᵣ Twkᵣ Tidᵣ ⟧σ (A ∷η η)) ≡ ⟦ σ ⟧σ η
⟦Twkᵣ⟧σ {[]} σ η A    = refl
⟦Twkᵣ⟧σ {ℓ ∷ Δ} σ η A = cong₂ _∷η_ 
  (trans (⟦Tren⟧T (A ∷η η) (Twkᵣ Tidᵣ) (σ ℓ (here refl))) (cong (λ η → ⟦ σ ℓ (here refl) ⟧T η) (trans (⟦Twkᵣ⟧ρ Tidᵣ η A) (⟦⟧ρ-Tidᵣ η)))) 
  (⟦Twkᵣ⟧σ (Tdropₛ σ) η A)

⟦Tidₛ⟧σ : (η : ⟦ Δ ⟧Δ) → (⟦ Tidₛ ⟧σ η) ≡ η
⟦Tidₛ⟧σ {[]}     η       = refl
⟦Tidₛ⟧σ {_ ∷ Δ₂} (A , η) = cong (A ∷η_) (trans (⟦Twkᵣ⟧σ Tidₛ η A) (⟦Tidₛ⟧σ η))

⟦Tsub⟧T : (η : ⟦ Δ₂ ⟧Δ) (σ : TSub Δ₁ Δ₂) (T : Type Δ₁ ℓ) → 
  ⟦ Tsub σ T ⟧T η ≡ ⟦ T ⟧T (⟦ σ ⟧σ η)
⟦Tsub⟧T η σ Nat       = refl
⟦Tsub⟧T η σ (` x)     = ⟦⟧Δ-lookup η σ x
  where ⟦⟧Δ-lookup : ∀ {ℓ} (η : ⟦ Δ₂ ⟧Δ) (σ : TSub Δ₁ Δ₂) (x : ℓ ∈ Δ₁) → 
                          (⟦ σ ℓ x ⟧T η) ≡ (⟦ ` x ⟧T (⟦ σ ⟧σ η))
        ⟦⟧Δ-lookup η σ (here refl) = refl
        ⟦⟧Δ-lookup η σ (there x) rewrite ⟦⟧Δ-lookup η (Tdropₛ σ) x = refl
⟦Tsub⟧T η σ (T₁ ⇒ T₂) rewrite ⟦Tsub⟧T η σ T₁ | ⟦Tsub⟧T η σ T₂ = refl
⟦Tsub⟧T η σ (∀α T)    = dep-ext λ A → 
  trans (⟦Tsub⟧T (A ∷η η) (Tliftₛ σ _) T) (cong (λ η → ⟦ T ⟧T (A , η)) (⟦Twkᵣ⟧σ σ η A))
  
data EEnv : (Δ : TEnv) → Set where
  []   : EEnv Δ
  _∷_  : Type Δ ℓ → EEnv Δ → EEnv Δ
  _∷ℓ_ : (ℓ : Level) → EEnv Δ → EEnv (ℓ ∷ Δ)

variable
  Γ Γ′ Γ₁ Γ₂ Γ₃ : EEnv Δ

data _∋_ : EEnv Δ → Type Δ ℓ → Set where
  here  : (T ∷ Γ) ∋ T
  there : Γ ∋ T → (T′ ∷ Γ) ∋ T
  tskip : Γ ∋ T → (ℓ ∷ℓ Γ) ∋ Twk T

⨆Γ : EEnv Δ → Level
⨆Γ []                = zero 
⨆Γ (_∷_ {ℓ = ℓ} T Γ) = ℓ ⊔ ⨆Γ Γ 
⨆Γ (ℓ ∷ℓ Γ)          = ⨆Γ Γ 

data Expr (Γ : EEnv Δ) : Type Δ ℓ → Set where
  `_   : Γ ∋ T → Expr Γ T
  #_   : ℕ → Expr Γ Nat
  ‵suc : Expr Γ Nat → Expr Γ Nat
  λx_  : Expr (T ∷ Γ) T′ → Expr Γ (T ⇒ T′)
  Λ_⇒_ : (ℓ : Level) {T : Type (ℓ ∷ Δ) ℓ′} → Expr (ℓ ∷ℓ Γ) T → Expr Γ (∀α T)
  _·_  : Expr Γ (T ⇒ T′) → Expr Γ T → Expr Γ T′
  _∙_  : Expr Γ (∀α T) → (T′ : Type Δ ℓ) → Expr Γ (T [ T′ ]T) 

module FunctionExprSemEnv where
  -- also works for semantic expression environments
  open import BoundQuantification as BQ
  
  Γ∋T⇒Tℓ≤⨆Γ : {T : Type Δ ℓ} {Γ : EEnv Δ} → Γ ∋ T → ℓ ≤ (⨆Γ Γ)
  Γ∋T⇒Tℓ≤⨆Γ {Γ = _ ∷ Γ} here = ≤-lub (⨆Γ Γ) (≤-id _)
  Γ∋T⇒Tℓ≤⨆Γ {Γ = _∷_ {ℓ = ℓ} _ Γ} (there x) = ≤-lub ℓ (Γ∋T⇒Tℓ≤⨆Γ x)
  Γ∋T⇒Tℓ≤⨆Γ {Γ = _ ∷ℓ Γ} (tskip x) = Γ∋T⇒Tℓ≤⨆Γ x
  
  ⟦_⟧Γ : (Γ : EEnv Δ) → ⟦ Δ ⟧Δ → Set (⨆Γ Γ)
  ⟦_⟧Γ Γ η = ∀ (ℓ : BoundLevel (suc (⨆Γ Γ))) (T : Type _ (BQ.# ℓ)) → (x : Γ ∋ T) → 
    BoundLift (Γ∋T⇒Tℓ≤⨆Γ x) ((⟦ T ⟧T η))

⟦_⟧Γ_   : (Γ : EEnv Δ) → ⟦ Δ ⟧Δ → Set (⨆Γ Γ)
⟦ []     ⟧Γ η = ⊤
⟦ T ∷ Γ  ⟧Γ η = ⟦ T ⟧T η × ⟦ Γ ⟧Γ η
⟦ ℓ ∷ℓ Γ ⟧Γ η = ⟦ Γ ⟧Γ (drop-η η) 
   
_∷γ_   : {η : ⟦ Δ ⟧Δ} → ⟦ T ⟧T η → ⟦ Γ ⟧Γ η → ⟦ T ∷ Γ ⟧Γ η
_∷γ_ = _,_

lookup-γ : {η : ⟦ Δ ⟧Δ} → ⟦ Γ ⟧Γ η → Γ ∋ T → ⟦ T ⟧T η 
lookup-γ (A , γ) here       = A
lookup-γ (_ , γ) (there x)  = lookup-γ γ x
lookup-γ {Γ = _ ∷ℓ Γ} {η = η} γ (tskip {T = T} x) = subst id (sym (⟦Tren⟧T η (Twkᵣ Tidᵣ) T)) 
  (lookup-γ (subst (λ η → ⟦ Γ ⟧Γ η) (sym (trans (⟦Twkᵣ⟧ρ Tidᵣ (proj₂ η) (proj₁ η)) (⟦⟧ρ-Tidᵣ (proj₂ η)))) γ) x)

⟦_⟧E : {Γ : EEnv Δ} → Expr Γ T → (η : ⟦ Δ ⟧Δ) → ⟦ Γ ⟧Γ η → ⟦ T ⟧T η
⟦ ` x     ⟧E η γ = lookup-γ γ x
⟦ # n     ⟧E η γ = n
⟦ ‵suc e  ⟧E η γ = sucℕ (⟦ e ⟧E η γ)
⟦_⟧E {T = (T₁ ⇒ T₂)} {Γ} (λx e) η γ = λ (x : ⟦ T₁ ⟧T η) → ⟦ e ⟧E η (_∷γ_ {T = T₁} {Γ = Γ} x γ)
⟦ Λ ℓ ⇒ e ⟧E η γ = λ (A : Set ℓ) → ⟦ e ⟧E (A ∷η η) γ
⟦ e₁ · e₂ ⟧E η γ = ⟦ e₁ ⟧E η γ (⟦ e₂ ⟧E η γ)
⟦ _∙_ {T = T} e T′ ⟧E η γ = subst id 
  (trans (cong (λ η′ → ⟦ T ⟧T ((⟦ T′ ⟧T η) , η′)) (sym (⟦Tidₛ⟧σ _))) (sym (⟦Tsub⟧T η _ T))) 
  (⟦ e ⟧E η γ (⟦ T′ ⟧T η)) 