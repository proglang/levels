module Universe where

module Lib where
  open import Data.Unit using (⊤; tt) public
  open import Data.Empty using (⊥; ⊥-elim) public
  open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂) public
  open import Data.Sum using (_⊎_; inj₁; inj₂) public
  open import Function hiding (id; _∘_; _⇔_) public
  open import Induction.WellFounded public
  open import Relation.Binary public
  open import Relation.Binary.PropositionalEquality
    hiding (decSetoid; preorder; setoid; [_]) public
  
  import Level as L
  module F where open import Function public
  
  coe : ∀ {α}{A B : Set α} → A ≡ B → A → B
  coe refl x = x
  
  _&_ = cong;  infixl 9 _&_; {-# DISPLAY cong  = _&_ #-}
  _◾_ = trans; infixr 4 _◾_; {-# DISPLAY trans = _◾_ #-}
  _⁻¹ = sym;   infix  6 _⁻¹; {-# DISPLAY sym   = _⁻¹ #-}
  
  coe∘ : ∀ {i}{A B C : Set i}(p : B ≡ C)(q : A ≡ B)(a : A)
         → coe p (coe q a) ≡ coe (q ◾ p) a
  coe∘ refl refl _ = refl
  
  UIP : ∀ {i}{A : Set i}{x y : A}{p q : x ≡ y} → p ≡ q
  UIP {p = refl}{refl} = refl
  
  -- function extensionality
  postulate
    ext : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x  ≡ g x) → f ≡ g
  
    exti : ∀{i j}{A : Set i}{B : A → Set j}{f g : ∀ {x} → B x}
            → ((x : A) → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ g
  
  unAcc : ∀ {α β A R i} → Acc {α}{β}{A} R i → ∀ {j} → R j i → Acc R j
  unAcc (acc f) = f
  
  Acc-prop : ∀ {α β A R i}(p q : Acc {α}{β}{A} R i) → p ≡ q
  Acc-prop (acc f) (acc g) = acc & exti λ j → ext λ p → Acc-prop (f p) (g p)
  
  happly : ∀ {α β}{A : Set α}{B : Set β}{f g : A → B} → f ≡ g → ∀ a → f a ≡ g a
  happly refl a = refl
  
  _⊗_ :
    ∀ {α β}{A : Set α}{B : Set β}
      {f g : A → B}(p : f ≡ g){a a' : A}(q : a ≡ a')
    → f a ≡ g a'
  refl ⊗ refl = refl
  infixl 8 _⊗_
  
  data W {α}{β}(A : Set α) (B : A → Set β) : Set (α L.⊔ β) where
    sup : (a : A) → (B a → W A B) → W A B


module IRUniverse where

  {-
  Inductive-recursive universes over arbitrary level structures.

  We give a full formalization of Section 4.1 of the paper.

  Additionally, we give some examples for type codes using ω and ω*ω levels.

  We also give a simple example for having _⊔_ operation on levels when levels
  form a type theoretic ordinal.
  -}

  open Lib

  -- set with well-founded transitive relation
  record LvlStruct : Set₁ where
    infix 4 _<_
    infixr 5 _∘_
    field
      Lvl         : Set
      _<_         : Lvl → Lvl → Set
      <-prop      : ∀ {i j}{p q : i < j} → p ≡ q
      _∘_         : ∀ {i j k} → j < k → i < j → i < k
      instance wf : ∀ {i} → Acc _<_ i

    acyclic : ∀ {i} → i < i → ⊥
    acyclic {i} p = go wf p where
      go : ∀ {i} → Acc _<_ i → i < i → ⊥
      go {i} (acc f) q = go (f q) q

  module IR-Universe (lvl : LvlStruct) where
    open LvlStruct lvl public
    open import Data.Nat hiding (_<_; _≤_)

    infix 4 _<'_
    infixr 1 _⊎'_

    data Uⁱʳ {i}(l : ∀ j → j < i → Set) : Set
    Elⁱʳ : ∀ {i l} → Uⁱʳ {i} l → Set

    data Uⁱʳ {i} l where
      U'       : ∀ {j} → j < i → Uⁱʳ l
      ℕ' ⊤' ⊥' : Uⁱʳ l
      _⊎'_     : Uⁱʳ l → Uⁱʳ l → Uⁱʳ l
      Π' Σ' W' : (a : Uⁱʳ l) → (Elⁱʳ a → Uⁱʳ l) → Uⁱʳ l

      -- codes for levels and morphisms, only used in level-polymorphic code examples
      Lvl'  : Uⁱʳ l
      _<'_  : Lvl → Lvl → Uⁱʳ l

    Elⁱʳ {_}{l}(U' p) = l _ p
    Elⁱʳ ℕ'           = ℕ
    Elⁱʳ ⊤'           = ⊤
    Elⁱʳ ⊥'           = ⊥
    Elⁱʳ Lvl'         = Lvl
    Elⁱʳ (i <' j)     = i < j
    Elⁱʳ (a ⊎' b)     = Elⁱʳ a ⊎ Elⁱʳ b
    Elⁱʳ (Π' a b)     = ∀ x → Elⁱʳ (b x)
    Elⁱʳ (Σ' a b)     = ∃ λ x → Elⁱʳ (b x)
    Elⁱʳ (W' a b)     = W (Elⁱʳ a) (λ x → Elⁱʳ (b x))


    -- Interpreting levels & lifts
    --------------------------------------------------------------------------------

    U< : ∀ {i} {{_ : Acc _<_ i}} j → j < i → Set
    U< {i} {{acc f}} j p = Uⁱʳ {j} (U< {j}{{f p}})

    U : Lvl → Set   -- semantic universe
    U i = Uⁱʳ {i} (U< {i} {{wf}})

    El : ∀ {i} → U i → Set
    El {i} = Elⁱʳ {i}{U< {i}{{wf}}}

    U<-compute : ∀ {i a j p} → U< {i}{{a}} j p ≡ U j
    U<-compute {i} {acc f} {j} {p} = (λ a → Uⁱʳ (U< {{a}})) & Acc-prop (f p) wf

    Lift   : ∀ {i j} → i < j → U i → U j
    ElLift : ∀ {i j} p a → El (Lift {i}{j} p a) ≡ El a
    Lift   p (U' q)      = U' (p ∘ q)
    Lift   p ℕ'          = ℕ'
    Lift   p ⊤'          = ⊤'
    Lift   p ⊥'          = ⊥'
    Lift   p Lvl'        = Lvl'
    Lift   p (i <' j)    = i <' j
    Lift   p (a ⊎' b)    = Lift p a ⊎' Lift p b
    Lift   p (Π' a b)    = Π' (Lift p a) λ x → Lift p (b (coe (ElLift p a) x))
    Lift   p (Σ' a b)    = Σ' (Lift p a) λ x → Lift p (b (coe (ElLift p a) x))
    Lift   p (W' a b)    = W' (Lift p a) λ x → Lift p (b (coe (ElLift p a) x))
    ElLift {i}{j} p (U' {k} q) = U<-compute {p = p ∘ q} ◾ U<-compute {p = q} ⁻¹
    ElLift p ℕ'       = refl
    ElLift p ⊤'       = refl
    ElLift p ⊥'       = refl
    ElLift p Lvl'     = refl
    ElLift p (i <' j) = refl
    ElLift p (a ⊎' b) = _⊎_ & ElLift p a ⊗ ElLift p b
    ElLift p (Π' a b) rewrite ElLift p a = (λ f → ∀ x → f x) & ext (ElLift p F.∘ b)
    ElLift p (Σ' a b) rewrite ElLift p a = Σ _ & ext (ElLift p F.∘ b)
    ElLift p (W' a b) rewrite ElLift p a = W _ & ext (ElLift p F.∘ b)

    -- congruence helper lemma
    congr2 : ∀ {i}{l : ∀ j → j < i → Set}
            (F' : (a : Uⁱʳ l) → (Elⁱʳ a → Uⁱʳ l) → Uⁱʳ l)
            {a₀ a₁ : Uⁱʳ l}(a₂ : a₀ ≡ a₁)
            {b₀ : Elⁱʳ a₀ → Uⁱʳ l}{b₁ : Elⁱʳ a₁ → Uⁱʳ l}
          → (∀ x → b₀ x ≡ b₁ (coe (Elⁱʳ & a₂) x))
          → F' a₀ b₀ ≡ F' a₁ b₁
    congr2 {i} {l} F' {a₀} refl {b₀} {b₁} b₂ = F' a₀ & ext b₂

    -- functorial lifting
    Lift∘ : ∀ {i j k}(p : i < j)(q : j < k) a → Lift q (Lift p a) ≡ Lift (q ∘ p) a
    Lift∘ p q (U' r)   = U' & <-prop
    Lift∘ p q ℕ'       = refl
    Lift∘ p q ⊤'       = refl
    Lift∘ p q ⊥'       = refl
    Lift∘ p q Lvl'     = refl
    Lift∘ p q (i <' j) = refl
    Lift∘ p q (a ⊎' b) = _⊎'_ & Lift∘ p q a ⊗ Lift∘ p q b
    Lift∘ p q (Π' a b) =
      congr2 Π' (Lift∘ p q a)
          (λ x → Lift∘ p q _
               ◾ (λ x → Lift (q ∘ p) (b x)) &
                    (coe∘ (ElLift p a) (ElLift q (Lift p a)) x
                  ◾ (λ y → coe y x) & UIP
                  ◾ coe∘ (ElLift (q ∘ p) a) (Elⁱʳ & Lift∘ p q a) x ⁻¹))
    Lift∘ p q (Σ' a b) =
      congr2 Σ' (Lift∘ p q a)
          (λ x → Lift∘ p q _
               ◾ (λ x → Lift (q ∘ p) (b x)) &
                    (coe∘ (ElLift p a) (ElLift q (Lift p a)) x
                  ◾ (λ y → coe y x) & UIP
                  ◾ coe∘ (ElLift (q ∘ p) a) (Elⁱʳ & Lift∘ p q a) x ⁻¹))
    Lift∘ p q (W' a b) =
      congr2 W' (Lift∘ p q a)
          (λ x → Lift∘ p q _
               ◾ (λ x → Lift (q ∘ p) (b x)) &
                    (coe∘ (ElLift p a) (ElLift q (Lift p a)) x
                  ◾ (λ y → coe y x) & UIP
                  ◾ coe∘ (ElLift (q ∘ p) a) (Elⁱʳ & Lift∘ p q a) x ⁻¹))

    -- conveniences
    --------------------------------------------------------------------------------

    _⇒'_ : ∀ {i l} → Uⁱʳ {i} l → Uⁱʳ l → Uⁱʳ l
    a ⇒' b = Π' a λ _ → b
    infixr 3 _⇒'_

    _×'_ : ∀ {i l} → Uⁱʳ {i} l → Uⁱʳ l → Uⁱʳ l
    a ×' b = Σ' a λ _ → b
    infixr 4 _×'_

    -- This is convenient in code examples, where we often want to lift values in Elⁱʳ U'
    LiftU : ∀ {i j}(p : i < j) → El (U' p) → U j
    LiftU p a = Lift p (coe U<-compute a)


  -- Type-theoretic ordinals
  --------------------------------------------------------------------------------

  record Ordinal (lvl : LvlStruct) : Set where
    open LvlStruct lvl
    field
      cmp    : ∀ i j → i < j ⊎ j < i ⊎ i ≡ j
      <-ext  : ∀ {i j} → (∀ k → (k < i → k < j) × (k < j → k < i)) → i ≡ j

    private
      pattern inj₂₁ x = inj₂ (inj₁ x)
      pattern inj₂₂ x = inj₂ (inj₂ x)

    _≤_ : Lvl → Lvl → Set; infix 4 _≤_
    i ≤ j = i < j ⊎ i ≡ j

    _⊔_ : Lvl → Lvl → Lvl; infixr 5 _⊔_
    i ⊔ j with cmp i j
    ... | inj₁  _ = j
    ... | inj₂₁ _ = i
    ... | inj₂₂ _ = i

    ⊔₁ : ∀ i j → i ≤ i ⊔ j
    ⊔₁ i j with cmp i j
    ... | inj₁  p = inj₁ p
    ... | inj₂₁ p = inj₂ refl
    ... | inj₂₂ p = inj₂ refl

    ⊔₂ : ∀ i j → j ≤ i ⊔ j
    ⊔₂ i j with cmp i j
    ... | inj₁  p = inj₂ refl
    ... | inj₂₁ p = inj₁ p
    ... | inj₂₂ p = inj₂ (p ⁻¹)

    ⊔-least : ∀ {i j k} → i ≤ k → j ≤ k → i ⊔ j ≤ k
    ⊔-least {i}{j}{k} p q with cmp i j
    ... | inj₁  _ = q
    ... | inj₂₁ _ = p
    ... | inj₂₂ _ = p

    ≤-prop : ∀ {i j}{p q : i ≤ j} → p ≡ q
    ≤-prop {p = inj₁ p}    {inj₁ q}    = inj₁ & <-prop
    ≤-prop {p = inj₁ p}    {inj₂ refl} = ⊥-elim (acyclic p)
    ≤-prop {p = inj₂ refl} {inj₁ q}    = ⊥-elim (acyclic q)
    ≤-prop {p = inj₂ p}    {inj₂ q}    = inj₂ & UIP

  module IR-Univ-Ordinal {lvl} (ord : Ordinal lvl) where
    open Ordinal ord public
    open IR-Universe lvl public

    -- non-strict lifts
    Lift≤ : ∀ {i j} → i ≤ j → U i → U j
    Lift≤ (inj₁ p)    a = Lift p a
    Lift≤ (inj₂ refl) a = a

    ElLift≤ : ∀ {i j} p a → El (Lift≤ {i}{j} p a) ≡ El a
    ElLift≤ (inj₁ p)    a = ElLift p a
    ElLift≤ (inj₂ refl) a = refl

    -- alternative Π type formation with _⊔_ and Lift.
    Π'' : ∀ {i j}(a : U i) → (El a → U j) → U (i ⊔ j)
    Π'' {i}{j} a b = Π' (Lift≤ (⊔₁ i j) a) λ x → Lift≤ (⊔₂ i j) (b (coe (ElLift≤ (⊔₁ i j) a) x))

module TTGUModel (L : IRUniverse.LvlStruct) where

  open import Data.Nat using (ℕ; zero; suc)
  open Lib
  open IRUniverse

  module IR = IR-Universe L
  open IR hiding (Lift; Lift∘)

  -- base category
  Con : Set₁
  Con = Set

  Sub : Con → Con → Set
  Sub Γ Δ = Γ → Δ

  idₛ : ∀ {Γ} → Sub Γ Γ
  idₛ γ = γ

  infixr 4 _∘ₛ_
  _∘ₛ_ : ∀ {Γ Δ ξ} → Sub Δ ξ → Sub Γ Δ → Sub Γ ξ
  σ ∘ₛ δ = λ γ → σ (δ γ)

  ∙ : Con
  ∙ = ⊤

  -- family diagram
  Ty : Con → Lvl → Set
  Ty Γ i = Γ → U i

  infixl 5 _[_]T
  _[_]T : ∀ {Γ Δ i} → Ty Δ i → Sub Γ Δ → Ty Γ i
  _[_]T A σ γ = A (σ γ)

  Tm : ∀ Γ {i} → Ty Γ i → Set
  Tm Γ A = (γ : Γ) → El (A γ)

  infixl 5 _[_]
  _[_] : ∀ {Γ Δ i A} → Tm Δ {i} A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
  _[_] t σ = λ γ → t (σ γ)

  infixl 3 _▶_
  _▶_ : ∀(Γ : Con){i} → Ty Γ i → Con
  Γ ▶ A = Σ Γ (λ γ → El (A γ))

  p : ∀ {Γ i}(A : Ty Γ i) → Sub (Γ ▶ A) Γ
  p A (γ , α) = γ

  q : ∀ {Γ i}(A : Ty Γ i) → Tm (Γ ▶ A) (A [ p A ]T)
  q A (γ , α) = α

  infixl 3 _,ₛ_
  _,ₛ_ : ∀ {Γ Δ}(σ : Sub Γ Δ){i A} → Tm Γ {i} (_[_]T {i = i} A σ) → Sub Γ (Δ ▶ A)
  _,ₛ_ σ t γ = (σ γ) , (t γ)

  Lift : ∀ {Γ i j} → i < j → Ty Γ i → Ty Γ j
  Lift p A γ = IR.Lift p (A γ)

  Lift∘ : ∀ {Γ i j k p q A} → Lift {Γ}{j}{k} p (Lift {Γ}{i}{j} q A) ≡ Lift (p ∘ q) A
  Lift∘ {p = p} {q} {A} = ext λ γ → IR.Lift∘ q p (A γ)

  lift[]T : ∀ {Γ Δ i j p σ A} → Lift {Δ}{i}{j} p A [ σ ]T ≡ Lift {Γ} p (A [ σ ]T)
  lift[]T = refl

  TmLift : ∀ {Γ i j p A} → Tm Γ A ≡ Tm Γ (Lift {Γ}{i}{j} p A)
  TmLift {p = p}{A} = (λ f → ∀ x → f x) & ext λ γ → ElLift p (A γ) ⁻¹

  ▶Lift : ∀ {Γ i j A}{p : i < j} → (Γ ▶ A) ≡ (Γ ▶ Lift p A)
  ▶Lift {Γ}{A = A}{p} = Σ Γ & ext λ γ → ElLift p (A γ) ⁻¹

  -- term lifting/lowering is definitionally the identity function in ETT
  -- also, since semantic term/type formers (with the exception of U) don't depend
  -- on levels, lifting/lowering preserves everything.
  lift : ∀ {Γ i j}(p : i < j){A : Ty Γ i} → Tm Γ A → Tm Γ (Lift p A)
  lift p {A} t = λ γ → coe (ElLift p (A γ) ⁻¹) (t γ)

  lower : ∀ {Γ i j}(p : i < j){A : Ty Γ i} → Tm Γ (Lift p A) → Tm Γ A
  lower p {A} t = λ γ → coe (ElLift p (A γ)) (t γ)

  -- universe
  Univ : ∀ {Γ i j} → i < j → Ty Γ j
  Univ p _ = U' p

  Univ[] : ∀ {Γ Δ σ i j p} → Univ {Δ}{i}{j} p [ σ ]T ≡ Univ {Γ}{i}{j} p
  Univ[] = refl

  RussellUniv : ∀ {Γ i j p} → Tm Γ (Univ {Γ}{i}{j} p) ≡ Ty Γ i
  RussellUniv = (λ f → ∀ x → f x) & ext λ _ → U<-compute

  -- some type formers
  Π : ∀ {Γ i}(A : Ty Γ i) → Ty (Γ ▶ A) i → Ty Γ i
  Π {Γ}{i} A B γ = Π' (A γ) λ α → B (γ , α)

  lam : ∀ {Γ i A B} → Tm (Γ ▶ A) B → Tm Γ {i} (Π A B)
  lam t γ α = t (γ , α)

  app : ∀ {Γ i A B} → Tm Γ {i} (Π A B) → Tm (Γ ▶ A) B
  app t (γ , α) = t γ α

  Nat : ∀ {Γ} i → Ty Γ i
  Nat i _ = ℕ' {i}

  LiftNat : ∀ {Γ i j p} → Lift {Γ}{i}{j} p (Nat i) ≡ Nat j
  LiftNat = refl

  Zero : ∀ {Γ i} → Tm Γ (Nat i)
  Zero _ = zero

  Suc : ∀ {Γ i} → Tm Γ (Nat i) → Tm Γ (Nat i)
  Suc t γ = suc (t γ)

  liftZero : ∀ {Γ i j p} → lift {Γ}{i}{j} p {Nat i} (Zero {Γ}{i}) ≡ (Zero {Γ}{j})
  liftZero = refl

  liftSuc : ∀ {Γ i j p t} → lift {Γ}{i}{j} p {Nat i} (Suc {Γ}{i} t) ≡ Suc {Γ}{j} (lift {Γ}{i}{j} p {Nat i} t)
  liftSuc = refl

module MutualOrdInstance where
  open import Relation.Binary.Definitions using (Irreflexive)
  open import Induction using (RecStruct)
  open import Induction.WellFounded using (WellFounded; WfRec)
  open import Ordinal
  open Lib
  open IRUniverse
  open import Function using (flip)


  --module Lex {A : Set a} {B : A → Set b}
  --                   (RelA : Rel A ℓ₁)
  --                   (RelB : ∀ x → Rel (B x) ℓ₂) where
  --                   
  --  infix 4 _<_
  --  data _<_ : Rel (Σ A B) (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
  --    left  : ∀ {x₁ y₁ x₂ y₂} (x₁<x₂ : RelA   x₁ x₂) → (x₁ , y₁) < (x₂ , y₂)
  --    right : ∀ {x y₁ y₂}     (y₁<y₂ : RelB x y₁ y₂) → (x  , y₁) < (x  , y₂)
--
  --  mutual
--
  --    accessible : ∀ {x y} →
  --                 Acc RelA x → (∀ {x} → WellFounded (RelB x)) →
  --                 Acc _<_ (x , y)
  --    accessible accA wfB = acc (accessible′ accA (wfB _) wfB)
--
--
  --    accessible′ :
  --      ∀ {x y} →
  --      Acc RelA x → Acc (RelB x) y → (∀ {x} → WellFounded (RelB x)) →
  --      WfRec _<_ (Acc _<_) (x , y)
  --    accessible′ (acc rsA) _    wfB (left  x′<x) = accessible (rsA x′<x) wfB
  --    accessible′ accA (acc rsB) wfB (right y′<y) =
  --      acc (accessible′ accA (rsB y′<y) wfB)
--
  --    wellFounded : WellFounded RelA → (∀ {x} → WellFounded (RelB x)) →
  --                  WellFounded _<_
  --    wellFounded wfA wfB p = accessible (wfA (proj₁ p)) wfB
--
  --    well-founded = wellFounded

  <-Rec : ∀{ℓ} → RecStruct MutualOrd ℓ ℓ
  <-Rec = WfRec _<_

  <-wellFounded : WellFounded _<_
  <-wellFounded′ : ∀ a → <-Rec (Acc _<_) a

  <-wellFounded a = acc (<-wellFounded′ a)
  <-wellFounded′ z {y} y<z = {!   !}

  -- <-wellFounded n = acc (<-wellFounded′ n)

  -- <-wellFounded′ ω^ γ + δ [ γ≥↑δ ] <₁            = acc λ { () }
  -- <-wellFounded′ ω^ γ + δ [ γ≥↑δ ] (<₂ {α = α} {β = β} {α≥↑β = α≥↑β} α<γ) with <-wellFounded′ γ α<γ 
  -- ... | a = {!   !} -- with <-wellFounded′ α γ<α 
  -- -- ... | hjkl = acc λ x → <-wellFounded′ (↑ β) {!   !} 
  -- <-wellFounded′ ω^ γ + δ [ γ≥↑δ ] (<₃ refl β<δ) = {!   !}

  lvl : LvlStruct
  lvl = record {
      Lvl    = MutualOrd
    ; _<_    = _<_
    ; <-prop = <IsPropValued _ _
    ; _∘_    = flip <-trans
    ; wf     = <-wellFounded _
    }
    
  open IR-Universe lvl hiding (_<_)
  
  <-extensional : {a b : MutualOrd} → ((c : MutualOrd) → (c < a → c < b) × (c < b → c < a)) → a ≡ b
  <-extensional {a} {b} f with <-tri a b | f a | f b 
  ... | inj₁ a<b         | _ , a<b→a<a | _ , _ = ⊥-elim (<-irrefl (a<b→a<a a<b))
  ... | inj₂ (inj₁ b<a)  | _ , _ | b<a→b<b , _ = ⊥-elim (<-irrefl (b<a→b<b b<a))
  ... | inj₂ (inj₂ refl) | _ , _ | _ , _       = refl
  
  ord : Ordinal lvl
  ord = record { 
      cmp   = <-tri 
    ; <-ext = <-extensional 
    } 
    
  open IR-Univ-Ordinal ord  