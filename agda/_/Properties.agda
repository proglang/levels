{-# OPTIONS --cubical #-}
private module Properties where

open import Lib.Ordinals.Preliminaries 
open import Lib.Ordinals.MutualOrd
open import Cubical.Foundations.Everything using (subst2)
    
-- first we need to define suc and _⊔_ for MutualOrd 
sucₒ : MutualOrd → MutualOrd
fst-ignores-suc : ∀ a → (fst a) ≡ fst (sucₒ a)

sucₒ 𝟎 = 𝟏
sucₒ ω^ a + b [ r ] = ω^ a + sucₒ b [ subst (a ≥_) (fst-ignores-suc b) r ]

fst-ignores-suc 𝟎              = refl
fst-ignores-suc ω^ a + b [ r ] = refl

_⊔ₒ_ : MutualOrd → MutualOrd → MutualOrd
a              ⊔ₒ 𝟎              = a
𝟎 ⊔ₒ              a              = a
ω^ a + b [ r ] ⊔ₒ ω^ c + d [ s ] with <-tri a c 
... | inj₁ _        = ω^ c + d [ s ]
... | inj₂ (inj₁ _) = ω^ a + b [ r ]
... | inj₂ (inj₂ _) with <-tri c d 
... | inj₁ _        = ω^ c + d [ s ]
... | inj₂ (inj₁ _) = ω^ a + b [ r ]
... | inj₂ (inj₂ _) = ω^ a + b [ r ]

-- now we can prove our laws
distributivity : ∀ (a b d : MutualOrd) (r : a ≥ fst (b ⊔ₒ d)) (s : a ≥ fst b) (t : a ≥ fst d) → 
  ω^ a + (b ⊔ₒ d) [ r ] ≡ ω^ a + b [ s ] ⊔ₒ ω^ a + d [ t ]
distributivity 𝟎 𝟎 𝟎 _ _ _ = MutualOrd⁼ refl refl 
distributivity 𝟎 𝟎 ω^ _ + _ [ _ ] _ _ _ = MutualOrd⁼ refl refl
distributivity 𝟎 ω^ _ + _ [ _ ] 𝟎 _ _ _ = MutualOrd⁼ refl refl
distributivity 𝟎 ω^ ba + bb [ ds ] ω^ da + db [ dt ] (inj₂ r) (inj₂ s) (inj₂ t) with <-tri ba da
... | inj₁ _            = MutualOrd⁼ refl refl
... | inj₂ (inj₁ da<ba) = ⊥-elim (≮𝟎 (subst2 _<_ (t ⁻¹) (s ⁻¹) da<ba))
... | inj₂ (inj₂ ba≡da) with <-tri da db
... | inj₁ _            = MutualOrd⁼ refl refl
... | inj₂ (inj₁ db<da) = ⊥-elim (≮𝟎 (subst (_ <_) (t ⁻¹) db<da))
... | inj₂ (inj₂ bb≡db) with dt | ds 
... | inj₁ ^db<da | _   = ⊥-elim (≮𝟎 (subst (_ <_) (t ⁻¹) ^db<da))
... | _ | inj₁ ^db<da   = ⊥-elim (≮𝟎 (subst (_ <_) (s ⁻¹) ^db<da))
... | inj₂ da≡^db | inj₂ ba≡^bb = MutualOrd⁼ refl (MutualOrd⁼ ba≡da {!   !})
distributivity ω^ a + a₁ [ x ] 𝟎 𝟎 r s t = {!   !} 
distributivity ω^ a + a₁ [ x ] 𝟎 ω^ d + d₁ [ x₁ ] r s t = {!   !}
distributivity ω^ a + a₁ [ x ] ω^ b + b₁ [ x₁ ] 𝟎 r s t = {!   !}   
distributivity ω^ a + a₁ [ x ] ω^ b + b₁ [ x₁ ] ω^ d + d₁ [ x₂ ] r s t = {!   !}  

¬a≤ω^a+b : ∀ (a b : MutualOrd) (r : a ≥ fst b) → ¬ (ω^ a + b [ r ] ≤ a)
¬a≤ω^a+b a b r (inj₁ x) = {!   !}
¬a≤ω^a+b a b r (inj₂ x) = {!   !}

subsumption₁₀ : ∀ (b a  : MutualOrd) (s : a ≥ fst b) → b ⊔ₒ ω^ a + b [ s ] ≡ ω^ a + b [ s ]
subsumption₁₀ 𝟎              a s = refl 
subsumption₁₀ ω^ b + d [ r ] a s with <-tri b a 
... | inj₁ _          = refl
... | inj₂ (inj₁ a<b) = ⊥-elim (Lm[≥→¬<] s a<b)
... | inj₂ (inj₂ b≡a) with <-tri a ω^ b + d [ r ]
... | inj₁ _          = refl  
... | inj₂ ω^b+d≤a    = ⊥-elim (¬a≤ω^a+b _ _ _ (subst (_ ≤_) (b≡a ⁻¹) ω^b+d≤a))

subsumption₁₁ : ∀ (b a  : MutualOrd) (s : a ≥ fst (sucₒ b)) → b ⊔ₒ ω^ a + sucₒ b [ s ] ≡ ω^ a + sucₒ b [ s ]
subsumption₁₁ 𝟎              a s = refl 
subsumption₁₁ ω^ b + d [ r ] a s with <-tri b a 
... | inj₁ _          = refl
... | inj₂ (inj₁ a<b) = ⊥-elim (Lm[≥→¬<] s a<b)
... | inj₂ (inj₂ b≡a) with <-tri a (sucₒ (ω^ b + d [ r ]))
... | inj₁ _          = refl  
... | inj₂ ω^b+d≤a    = ⊥-elim (¬a≤ω^a+b _ _ _ (subst (_ ≤_) (b≡a ⁻¹) ω^b+d≤a)) 

--  module CNF-example where
-- open import Lib.Universes.Lib
-- open import Lib.Universes.IRUniverse
-- 
-- open import Relation.Binary.Definitions using (Irreflexive)
-- open import Induction using (RecStruct)
-- open import Induction.WellFounded using (WellFounded; WfRec)


-- 
-- <-Rec : ∀{a : MutualOrd} → RecStruct MutualOrd a a
-- <-Rec = WfRec _<_
-- 
-- postulate
--   <-wellFounded : WellFounded _<_
--   <-wellFounded′ : ∀ α → <-Rec (Acc _<_) α
-- --
-- --  -- <-wellFounded n = acc (<-wellFounded′ n)
-- --
-- --  -- <-wellFounded′ ω^ γ + δ [ γ≥↑δ ] <₁            = acc λ { () }
-- --  -- <-wellFounded′ ω^ γ + δ [ γ≥↑δ ] (<₂ {α = α} {β = β} {α≥↑β = α≥↑β} α<γ) with <-wellFounded′ γ α<γ 
-- --  -- ... | a = {!   !} -- with <-wellFounded′ α γ<α 
-- --  -- -- ... | hjkl = acc λ x → <-wellFounded′ (↑ β) {!   !} 
-- --  -- <-wellFounded′ ω^ γ + δ [ γ≥↑δ ] (<₃ refl β<δ) = {!   !}
-- --
-- lvl : LvlStruct
-- lvl = record {
--     Lvl    = CNF
--   ; _<_    = _<_
--   ; <-prop = <-irrelevant _ _
--   ; _∘_    = <-transitivity
--   ; wf     = <-wellFounded _
--   }
-- --    
-- open IR-Universe lvl hiding (_<_)
-- --  
-- postulate
--   <-compare : (α β : CNF) → (α < β) ⊎ (β < α) ⊎ α ≡ β
-- -- <-compare 𝟎                 𝟎                 = inj₂ (inj₂ refl)
-- -- <-compare 𝟎                 ω^ _ + _ [ _ ]    = inj₁ <₁
-- -- <-compare ω^ _ + _ [ _ ]    𝟎                 = inj₂ (inj₁ <₁)
-- -- <-compare ω^ α + β [ α≥↑β ] ω^ γ + δ [ γ≥↑δ ] with <-compare α γ 
-- -- ... | inj₁ α<γ         = inj₁ (<₂ α<γ)
-- -- ... | inj₂ (inj₁ γ<α)  = inj₂ (inj₁ (<₂ γ<α))
-- -- ... | inj₂ (inj₂ refl) with <-compare β δ 
-- -- ... | inj₁ β<δ         = inj₁ (<₃ refl β<δ)
-- -- ... | inj₂ (inj₁ δ<β)  = inj₂ (inj₁ (<₃ refl δ<β))
-- -- ... | inj₂ (inj₂ refl) = {!   !} -- todo α≥↑β proof is unique 
-- --
--   <-extensional : {α β : CNF} → ((γ : CNF) → (γ < α → γ < β) × (γ < β → γ < α)) → α ≡ β
-- --  -- <-extensional = {!   !}
-- --  
-- ord : Ordinal lvl
-- ord = record { 
--     cmp   = <-compare 
--   ; <-ext = <-extensional 
--   } 
-- open IR-Univ-Ordinal ord 