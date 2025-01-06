module ordinals where

open import Data.Sum using (_⊎_; inj₁; inj₂) 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

infix 30 _<_ _≤_ _>_ _≥_

data CNF : Set
data _<_ : CNF → CNF → Set
↑_ : CNF → CNF

_>_ _≥_ _≤_ : CNF → CNF → Set
α > β = β < α
α ≥ β = α > β ⊎ α ≡ β
α ≤ β = β ≥ α

data CNF where
 𝟎 : CNF
 ω^_+_[_] : (α β : CNF) → α ≥ (↑ β) → CNF

variable
  α β γ δ : CNF
  α≥↑β : α ≥ (↑ β)
  γ≥↑δ : γ ≥ (↑ δ)

data _<_ where
 <₁ : 𝟎 < ω^ α + β [ α≥↑β ]
 <₂ : α < γ → ω^ α + β [ α≥↑β ] < ω^ γ + δ [ γ≥↑δ ]
 <₃ : α ≡ γ → β < δ → ω^ α + β [ α≥↑β ] < ω^ γ + δ [ γ≥↑δ ]

↑ 𝟎                = 𝟎
↑ (ω^ α + _ [ _ ]) = α

≥𝟎 : α ≥ 𝟎
≥𝟎 {𝟎}              = inj₂ refl
≥𝟎 {ω^ α + β [ _ ]} = inj₁ <₁

ω^⟨_⟩ : CNF → CNF
ω^⟨ a ⟩ = ω^ a + 𝟎 [ ≥𝟎 ]

𝟏 ω : CNF
𝟏 = ω^⟨ 𝟎 ⟩
ω = ω^⟨ 𝟏 ⟩

0≮0 : ¬ (𝟎 < 𝟎)
0≮0 = λ { () }

↑-preserves-< : α < β → (↑ α) ≤ (↑ β) 
↑-preserves-< <₁          = {!   !}
↑-preserves-< (<₂ α<γ)    = inj₁ α<γ
↑-preserves-< (<₃ refl _) = inj₂ refl

transitivity : α < β → β < γ → α < γ 
transitivity <₁           (<₂ β<γ)       = <₁
transitivity <₁           (<₃ x β<γ)     = <₁
transitivity (<₂ α<β)     (<₂ β<γ)       = <₂ (transitivity α<β β<γ)
transitivity (<₂ α<γ)     (<₃ refl _)    = <₂ α<γ
transitivity (<₃ refl _)  (<₂ α<γ)       = <₂ α<γ
transitivity (<₃ refl α<β) (<₃ refl β<γ) = <₃ refl (transitivity α<β β<γ)

transitivity-≥ : α ≥ β → β ≥ γ → α ≥ γ 
transitivity-≥ (inj₁ α>β)  (inj₁ β>γ)  = inj₁ (transitivity β>γ α>β)
transitivity-≥ (inj₁ α>β)  (inj₂ refl) = inj₁ α>β
transitivity-≥ (inj₂ refl) (inj₁ β>γ)  = inj₁ β>γ
transitivity-≥ (inj₂ refl) (inj₂ refl) = inj₂ refl

suc : CNF → CNF 
α≥↑β-ignores-suc : α ≥ (↑ β) →  α ≥ (↑ suc β) 
suc 𝟎                 = 𝟏
suc ω^ α + β [ α≥↑β ] = ω^ α + suc β [ {!   !} ]
α≥↑β-ignores-suc (inj₁ x)    = {!   !}
α≥↑β-ignores-suc (inj₂ refl) = {!   !}  

α<suc-α : ∀ α →  α < suc α 
α<suc-α 𝟎                 = <₁
α<suc-α ω^ α + β [ α≥↑β ] = <₃ refl (α<suc-α β)

_≡?_ : (α β : CNF) → Dec (α ≡ β)
𝟎                 ≡? 𝟎              = yes refl
𝟎                 ≡? ω^ _ + _ [ _ ] = no (λ ())
ω^ _ + _ [ _ ]    ≡? 𝟎              = no (λ ())
ω^ α + β [ α≥↑β ] ≡? ω^ γ + δ [ γ≥↑δ ] with α ≡? γ | β ≡? δ 
... | yes refl | yes refl = yes {!   !}
... | no α≠γ   | _        = no λ { refl → α≠γ refl }
... | _        | no β≠δ   = no λ { refl → β≠δ refl }

_<?_ : (α β : CNF) → Dec (α < β)  
𝟎               <? 𝟎              = no λ ()
𝟎               <? ω^ _ + _ [ _ ] = yes <₁ 
ω^ _ + _ [ _ ]  <? 𝟎              = no λ () 
ω^ α + β [ α≥↑β ] <? ω^ γ + δ [ γ≥↑δ ] with α <? γ 
... | yes α<γ  = yes (<₂ α<γ)
... | no α≮γ   with α ≡? γ 
... | no a≠γ   = no λ where
  (<₂ α<γ)   → α≮γ α<γ 
  (<₃ a≡γ _) → a≠γ a≡γ 
... | yes refl with β <? δ 
... | yes β<δ  = yes (<₃ refl β<δ)
... | no β≮δ   = no λ where
  (<₂ a<γ)   → α≮γ a<γ
  (<₃ _ β<δ) → β≮δ β<δ 

_⊔_ : (α β : CNF) → CNF
α ⊔ 𝟎 = α
𝟎 ⊔ β = β
ω^ α + β [ α≥↑β ] ⊔ ω^ γ + δ [ γ≥↑δ ] with α <? β 
... | yes _ = ω^ γ + δ [ γ≥↑δ ]
... | no _  = ω^ α + β [ α≥↑β ]

idempotence : α ⊔ α ≡ α 
idempotence {𝟎}                 = refl
idempotence {ω^ α + β [ α≥↑β ]} with α <? β 
... | yes _ = refl
... | no _  = refl
     