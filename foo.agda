module foo where 

data Nat : Set where
  zero : Nat
  suc : Nat → Nat

data List : Set where
  [] : List
  _∷_ : Nat → List → List

data _∈_ : Nat → List → Set where
  here : ∀ {x} {xs} → x ∈ (x ∷ xs)
  there : ∀ {x} {y} {xs} → x ∈ xs → x ∈ (y ∷ xs)

data _<_ : Nat → Nat → Set where
  <₁ : ∀ {x} → zero < x
  <₂ : ∀ {x} {y} → x < y → suc x < suc y

_⊔_ : Nat → Nat → Nat
zero ⊔ y = y
x ⊔ zero = x
suc x ⊔ suc y = suc (x ⊔ y)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
right-id : ∀ {x} → x ≡ x ⊔ zero
right-id {zero} = refl
right-id {suc x} = refl

commutativity : ∀ {x} {y} → x ⊔ y ≡ y ⊔ x
commutativity {zero} {y} = right-id
commutativity {suc x} {zero} = refl
commutativity {suc x} {suc y} = cong suc (commutativity {x} {y}) 

lvl : List → Nat
lvl [] = zero   
lvl (x ∷ xs) = suc x ⊔ lvl xs

trans : ∀ {x} {y} {z} → x < y → y < z → x < z
trans <₁ y<z = <₁
trans (<₂ x<y) (<₂ y<z) = <₂ (trans x<y y<z)

lemma₁ : ∀ {x} → x < suc x 
lemma₁ {zero}  = <₁
lemma₁ {suc x} = <₂ lemma₁

subsumption : ∀ {x} {y} {z} → x < y → x < (y ⊔ z)
subsumption {x} {y} {z} <₁       = <₁
subsumption {x} {suc y} {zero} x<y = x<y
subsumption {x} {suc y} {suc z} (<₂ x<y) = <₂ (subsumption {z = z} x<y)

lemma : ∀ {x} {xs} → x ∈ xs → x < lvl xs
lemma {_} {_ ∷ xs} here      = subsumption {z = lvl xs} lemma₁
lemma {_} {y ∷ xs} (there x) = subst (_ <_) (commutativity {lvl xs} {suc y}) (subsumption (lemma x)) 