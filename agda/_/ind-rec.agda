module ind-rec where
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃-syntax)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_) 
open import Data.Nat.Properties using (+-identityʳ; +-suc; ⊔-identityʳ; ⊔-comm)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Function using (id)

Fam : Set₁ → Set₁
Fam X = Σ Set λ I → I → X

data U (X : Fam Set) : Set 
⟦_⟧U : ∀ {X} → U X → Set

data U X where 
    U′ : U X
    El′ : proj₁ X → U X
    Nat′ : U X
    Π′ Σ′ : (S : U X) (T : ⟦ S ⟧U → U X) → U X
    
⟦_⟧U {U , El} U′ = U
⟦_⟧U {U , El}(El′ T) = El T
⟦ Nat′ ⟧U = ℕ
⟦ Π′ S T ⟧U = (s : ⟦ S ⟧U) → ⟦ T s ⟧U
⟦ Σ′ S T ⟧U = Σ (⟦ S ⟧U) λ s → ⟦ T s ⟧U

EMPTY : Fam Set
EMPTY = ⊥ , (λ{()})

-- this definition does not reduce to a pair as long as the level is unknown
LEVEL′ : ℕ → Fam Set
LEVEL′ zero = U EMPTY , ⟦_⟧U
LEVEL′ (suc n) = U (LEVEL′ n) , ⟦_⟧U

CODE′ : ℕ → Set
CODE′ l = proj₁ (LEVEL′ l)

LEVEL go : ℕ → Fam Set
LEVEL l = U (go l) , ⟦_⟧U
go zero = EMPTY
go (suc n) = LEVEL n

CODE : ℕ → Set
CODE l = proj₁ (LEVEL l)

-- stratified system f

open import Data.List using (List; []; _∷_)
open import Level using ()

variable ℓ ℓ′ ℓ₁ ℓ₂ : ℕ

Env = List ℕ
variable Δ Δ′ Δ₁ Δ₂ : Env

data _∈_ : ℕ → Env → Set where
    here   : ℓ ∈ (ℓ ∷ Δ)
    there  : ℓ ∈ Δ → ℓ ∈ (ℓ′ ∷ Δ)

Δ-level : Env → ℕ
Δ-level [] = 0
Δ-level (ℓ ∷ Δ) = suc ℓ ⊔ Δ-level Δ


data Type Δ : ℕ → Set where
  `ℕ      : Type Δ zero
  _⇒_     : (T₁ : Type Δ ℓ₁) (T₂ : Type Δ ℓ₂) → Type Δ (ℓ₁ ⊔ ℓ₂)
  `_      : (α : ℓ ∈ Δ) → Type Δ ℓ
  `∀α_,_  : (ℓ : ℕ) (T : Type (ℓ ∷ Δ) ℓ′) → Type Δ (suc ℓ ⊔ ℓ′)

lift : U (LEVEL ℓ) → U (LEVEL (ℓ′ ⊔ ℓ))
lift {ℓ}     {zero}   v = v
lift {zero}  {suc ℓ′} v = {! El′ (lift {zero} {ℓ′} v)  !}
lift {suc ℓ} {suc ℓ′} v = {!   !}

lift′ : U (LEVEL ℓ) → U (LEVEL (ℓ ⊔ ℓ′))
lift′ {ℓ} {ℓ′} x = subst (λ ℓ → U (LEVEL ℓ)) (⊔-comm ℓ′ ℓ) (lift x)
 
variable T T′ T₁ T₂ : Type Δ ℓ

Env* : Env → Set
Env* Δ = ∀ {ℓ} → ℓ ∈ Δ → U (LEVEL ℓ)

_∷*_ : U (LEVEL ℓ) → Env* Δ → Env* (ℓ ∷ Δ) 
(_∷*_) {ℓ = ℓ} {Δ = Δ} S η here = S
(S ∷* η) (there x) = η x
  
variable
  η η′ η₁ η₂ : Env* Δ  

-- ⟦_⟧ : (T : Type Δ l) → Env* Δ → Set l
-- ⟦ `ℕ         ⟧ η = ℕ
-- ⟦ T₁ ⇒ T₂    ⟧ η = ⟦ T₁ ⟧ η → ⟦ T₂ ⟧ η
-- ⟦ ` α        ⟧ η = lookup α η  
-- ⟦ `∀α l , T  ⟧ η = (α : Set l) → ⟦ T ⟧ (α ∷ η)

-- still wrong
encode : Type Δ ℓ → Env* Δ → U (LEVEL ℓ) 
encode `ℕ η = Nat′
encode (_⇒_ {ℓ₁}{ℓ₂} T₁ T₂) η = Π′ {! lift′ (encode T₁ η)  !} λ _ → {! lift (encode T₂ η)  !}
encode (` x) η = η x 
encode (`∀α_,_ {ℓ′ = ℓ′} ℓ T₁) η = Π′ (lift′ {ℓ′ = ℓ′} (U′ {X = LEVEL (suc ℓ)})) (λ x → (lift (encode T₁ ({! x  !} ∷* η))))

⟦_⟧ : (T : Type Δ ℓ) (η : Env* Δ) → Set
⟦ T ⟧ η = ⟦ encode T η ⟧U
       