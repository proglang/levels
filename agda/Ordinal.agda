-- ###################################
-- ## BEGIN CODE FROM ORDINAL PAPER ##
-- ###################################

--! O >

module Ordinal where

open import Data.Sum using (_⊎_; inj₁; inj₂) 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; subst; subst₂) renaming (sym to _⁻¹; trans to _∙_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Level using(Level)

private variable
  ℓ : Level

infix 30 _<_ _≤_ _>_ _≥_

data MutualOrd : Set
fst : MutualOrd → MutualOrd

data _<_ : MutualOrd → MutualOrd → Set
_>_ _≥_ _≤_ : MutualOrd → MutualOrd → Set
a > b = b < a

--!! GtDef 
a ≥ b = a > b ⊎ a ≡ b

a ≤ b = b ≥ a

--! MDef 
data MutualOrd where
  𝟎         : MutualOrd
  ω^_+_[_]  : (a b : MutualOrd) → a ≥ fst b → MutualOrd

private variable
  a b c d : MutualOrd
  r : a ≥ fst b
  s : c ≥ fst d

--! OrdDef
data _<_ where
  <₁ : 𝟎 < ω^ a + b [ r ]
  <₂ : a < c → ω^ a + b [ r ] < ω^ c + d [ s ]
  <₃ : a ≡ c → b < d → ω^ a + b [ r ] < ω^ c + d [ s ]

--! fstDef
fst  𝟎               = 𝟎
fst (ω^ a + _ [ _ ]) = a

rest : MutualOrd → MutualOrd
rest  𝟎               = 𝟎
rest (ω^ _ + b [ _ ]) = b

caseMutualOrd : {A : Set ℓ} (x y : A) → MutualOrd → A
caseMutualOrd x y  𝟎               = x
caseMutualOrd x y (ω^ _ + _ [ _ ]) = y

𝟎≢ω : {r : a ≥ fst b} → ¬ (𝟎 ≡ ω^ a + b [ r ])
𝟎≢ω e = subst (caseMutualOrd MutualOrd ⊥) e 𝟎

ω≢𝟎 : {r : a ≥ fst b} → ¬ (ω^ a + b [ r ] ≡ 𝟎)
ω≢𝟎 e = subst (caseMutualOrd ⊥ MutualOrd) e 𝟎

<-irrefl : ¬ a < a
<-irrefl (<₂ r)     = <-irrefl r
<-irrefl (<₃ a=a r) = <-irrefl r

<-irreflexive : a ≡ b → ¬ a < b
<-irreflexive {a} e = subst (λ x → ¬ a < x) e <-irrefl

<IsPropValued : (p q : a < b) → p ≡ q
<IsPropValued <₁ <₁                   = refl
<IsPropValued (<₂ p) (<₂ q)           = cong <₂ (<IsPropValued p q)
<IsPropValued (<₂ p) (<₃ r q)         = ⊥-elim (<-irreflexive r p)
<IsPropValued (<₃ r p) (<₂ q)         = ⊥-elim (<-irreflexive r q)
<IsPropValued (<₃ refl p) (<₃ refl q) = cong (<₃ _) (<IsPropValued p q)

≤IsPropValued : (p q : a ≤ b) → p ≡ q
≤IsPropValued (inj₁ p) (inj₁ q)       = cong inj₁ (<IsPropValued p q)
≤IsPropValued (inj₁ p) (inj₂ e)       = ⊥-elim (<-irreflexive (e ⁻¹) p)
≤IsPropValued (inj₂ e) (inj₁ q)       = ⊥-elim (<-irreflexive (e ⁻¹) q)
≤IsPropValued (inj₂ refl) (inj₂ refl) = refl

MutualOrd⁼ : {r : a ≥ fst b} {s : c ≥ fst d} → a ≡ c → b ≡ d
           → ω^ a + b [ r ] ≡ ω^ c + d [ s ]
MutualOrd⁼ {r = r} {s = s} refl refl = cong ω^ _ + _ [_] (≤IsPropValued r s)

<-tri : (a b : MutualOrd) → a < b ⊎ a ≥ b
<-tri  𝟎                𝟎               = inj₂ (inj₂ refl)
<-tri  𝟎               (ω^ b + d [ _ ]) = inj₁ <₁
<-tri (ω^ a + c [ _ ])  𝟎               = inj₂ (inj₁ <₁)
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) with <-tri a b
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₁       a<b  = inj₁ (<₂ a<b)
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₂ (inj₁ a>b) = inj₂ (inj₁ (<₂ a>b))
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₂ (inj₂ a=b) with <-tri c d
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₂ (inj₂ a=b) | inj₁       c<d  = inj₁ (<₃ a=b c<d)
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₂ (inj₂ a=b) | inj₂ (inj₁ c>d) = inj₂ (inj₁ (<₃ (a=b ⁻¹) c>d))
<-tri (ω^ a + c [ _ ]) (ω^ b + d [ _ ]) | inj₂ (inj₂ a=b) | inj₂ (inj₂ c=d) = inj₂ (inj₂ (MutualOrd⁼ a=b c=d))

<-trans : a < b → b < c → a < c
<-trans  <₁      (<₂ _)   = <₁
<-trans  <₁      (<₃ _ _) = <₁
<-trans (<₂ r)   (<₂ s)   = <₂ (<-trans r s)
<-trans (<₂ r)   (<₃ p _) = <₂ (subst (λ x → _ < x) p r)
<-trans (<₃ p _) (<₂ s)   = <₂ (subst (λ x → x < _) (p ⁻¹) s)
<-trans (<₃ p r) (<₃ q s) = <₃ (p ∙ q) (<-trans r s)

≤-trans : a ≤ b → b ≤ c → a ≤ c
≤-trans (inj₁ a<b) (inj₁ b<c) = inj₁ (<-trans a<b b<c)
≤-trans (inj₁ a<b) (inj₂ c=b) = inj₁ (subst (λ x → _ < x) (c=b ⁻¹) a<b)
≤-trans (inj₂ b=a) (inj₁ b<c) = inj₁ (subst (λ x → x < _) b=a b<c)
≤-trans (inj₂ b=a) (inj₂ c=b) = inj₂ (c=b ∙ b=a)

<≤-trans : a < b → b ≤ c → a < c
<≤-trans a<b (inj₁ b<c) = <-trans a<b b<c
<≤-trans a<b (inj₂ c≡b) = subst (_ <_) (c≡b ⁻¹) a<b

Lm[≥→¬<] : a ≥ b → ¬ a < b
Lm[≥→¬<] (inj₁ b<a) a<b = <-irrefl (<-trans a<b b<a)
Lm[≥→¬<] (inj₂ a=b)     = <-irreflexive a=b

Lm[<→¬≥] : a < b → ¬ a ≥ b
Lm[<→¬≥] a<b (inj₁ a>b) = <-irrefl (<-trans a<b a>b)
Lm[<→¬≥] a<b (inj₂ a=b) = <-irreflexive a=b a<b

Lm[¬<→≥] : ¬ a < b → a ≥ b
Lm[¬<→≥] f with <-tri _ _
Lm[¬<→≥] f | inj₁       a<b  = ⊥-elim (f a<b)
Lm[¬<→≥] f | inj₂ (inj₁ a>b) = inj₁ a>b
Lm[¬<→≥] f | inj₂ (inj₂ a=b) = inj₂ a=b

<-dec : (a b : MutualOrd) → a < b ⊎ ¬ a < b
<-dec a b with <-tri a b
<-dec a b | inj₁ a<b = inj₁ a<b
<-dec a b | inj₂ a≥b = inj₂ (Lm[≥→¬<] a≥b)

<-≡ : {a b c : MutualOrd} → a < b → b ≡ c → a < c
<-≡ {a} e r = subst (a <_) r e

≤≥→≡ : a ≤ b → a ≥ b → a ≡ b
≤≥→≡ a≤b (inj₁ a>b) = ⊥-elim (Lm[<→¬≥] a>b a≤b)
≤≥→≡ a≤b (inj₂ a=b) = a=b

≮𝟎 : ¬ a < 𝟎
≮𝟎 ()

≥𝟎 : a ≥ 𝟎
≥𝟎 {𝟎}              = inj₂ refl
≥𝟎 {ω^ a + b [ _ ]} = inj₁ <₁

fst< : (a b : MutualOrd) (r : a ≥ fst b)
     → a < ω^ a + b [ r ]
fst<  𝟎               b r = <₁
fst< (ω^ a + c [ s ]) b r = <₂ (fst< a c s)

rest< : (a b : MutualOrd) (r : a ≥ fst b)
      → b < ω^ a + b [ r ]
rest< a  𝟎                _       = <₁
rest< a (ω^ b + c [ s ]) (inj₁ r) = <₂ r
rest< a (ω^ b + c [ s ]) (inj₂ e) = <₃ (e ⁻¹) (rest< b c s)

open import Induction.WellFounded

𝟎Acc : Acc _<_ 𝟎
𝟎Acc = acc (λ x<𝟎 → ⊥-elim (≮𝟎 x<𝟎))

fstAcc : ∀ {a a'} → Acc _<_ a' → a ≡ a'
  → ∀ {b x} → Acc _<_ b → x < a' → (r : x ≥ fst b)
  → Acc _<_ (ω^ x + b [ r ])
sndAcc : ∀ {a a'} → Acc _<_ a' → a ≡ a'
  → ∀ {c y} → Acc _<_ c → y < c → (r : a ≥ fst y)
  → Acc _<_ (ω^ a + y [ r ])

fstAcc {a} {a'} (acc ξ) a=a' {b} {x} acᵇ x<a r = acc goal
  where
   goal : ∀ {z} → z < ω^ x + b [ r ] → Acc _<_ z
   goal {𝟎} <₁ = 𝟎Acc
   goal {ω^ c + d [ s ]} (<₂ c<y) = fstAcc (ξ x<a) refl (goal {d} (<-trans (rest< c d s) (<₂ c<y))) c<y s
   goal {ω^ c + d [ s ]} (<₃ c=y d<b) = sndAcc (ξ x<a) c=y acᵇ d<b s

sndAcc {a} {a'} acᵃ a=a' {c} {y} (acc ξᶜ) y<c r = acc goal
  where
   goal : ∀ {z} → z < ω^ a + y [ r ] → Acc _<_ z
   goal {𝟎} <₁ = 𝟎Acc
   goal {ω^ b + d [ t ]} (<₂ b<a) = fstAcc acᵃ a=a' (goal {d} (<-trans (rest< b d t) (<₂ b<a))) (subst (b <_) a=a' b<a) t
   goal {ω^ b + d [ t ]} (<₃ b=a d<y) = sndAcc acᵃ (b=a ∙ a=a') (ξᶜ y<c) d<y t

ω+Acc : (a b : MutualOrd) (r : a ≥ fst b)
      →  Acc _<_ a →  Acc _<_ b → Acc _<_ (ω^ a + b [ r ])
ω+Acc a b r acᵃ acᵇ = acc goal
 where
  goal : ∀ {z} → z < ω^ a + b [ r ] → Acc _<_ z
  goal {𝟎} <₁ = 𝟎Acc
  goal {ω^ c + d [ s ]} (<₂ c<a) = fstAcc acᵃ refl (goal {d} (<-trans (rest< c d s) (<₂ c<a))) c<a s
  goal {ω^ c + d [ s ]} (<₃ c=a d<b) = sndAcc acᵃ c=a acᵇ d<b s

WF : (x : MutualOrd) → Acc _<_ x
WF 𝟎 = 𝟎Acc
WF (ω^ a + b [ r ]) = ω+Acc a b r (WF a) (WF b)

-- #################################
-- ## END CODE FROM ORDINAL PAPER ##
-- #################################