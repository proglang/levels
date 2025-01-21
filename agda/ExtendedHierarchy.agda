open import Agda.Builtin.Equality using (_≡_; refl)
open import Level

-- we postulate the existence of ordinals in cantor normal form (cnf).
-- this constructor does not check the so called cnf property (exponents in the base-ω sum monotonely decrease).
-- thus, we should use a `private postulate`
-- but we keep it public, so we can prove level equalities that would in normally be solved by the compiler
-- in an actual implementation we only would expose the safe MutualOrd interface as described below
infix 40 ω^_+_
postulate
  ω^_+_ : (ℓ₁ ℓ₂ : Level) → Level

-- with symbols for valid ordinals in cnf our hierarchy grows to ε₀
Setε₀ = Setω

-- safe interface for constructing ordinals in cnf that fulfill the cnf property
open import Ordinal public
⌊_⌋ : MutualOrd → Level
⌊ 𝟎 ⌋                = zero
⌊ ω^ l₁ + l₂ [ _ ] ⌋ = ω^ ⌊ l₁ ⌋ + ⌊ l₂ ⌋

private variable
  ℓ ℓ′ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  
postulate
  -- by definition
  β-suc-zero : suc zero ≡ ω^ zero + zero
  β-suc-ω    : suc (ω^ ℓ₁ + ℓ₂) ≡ ω^ ℓ₁ + suc ℓ₂
  -- compiler laws to solve level (in-)equalities
  -- the laws are in addition to the already given intrinsic level properties that Agda currently uses to solve level (in-)equalities
  -- see: https://agda.readthedocs.io/en/latest/language/universe-levels.html#intrinsic-level-properties
  -- the laws are proven blow in the _Laws module at the end of the file using the MutualOrd representation
  distributivity : ω^ ℓ + (ℓ₁ ⊔ ℓ₂) ≡ ω^ ℓ + ℓ₁ ⊔ ω^ ℓ + ℓ₂ 
  subsumption₁₀ : ℓ ⊔ ω^ ℓ₁ + ℓ ≡ ω^ ℓ₁ + ℓ
  subsumption₁₁ : ℓ ⊔ ω^ ℓ₁ + suc ℓ ≡ ω^ ℓ₁ + suc ℓ
  subsumption₂₀ : ℓ ⊔ ω^ ℓ₁ + ω^ ℓ₂ + ℓ ≡ ω^ ℓ₁ + ω^ ℓ₂ + ℓ
  subsumption₂₁ : ℓ ⊔ ω^ ℓ₁ + ω^ ℓ₂ + suc ℓ ≡ ω^ ℓ₁ + ω^ ℓ₂ + suc ℓ
  -- in reality the Agda compiler would apply an infinite set of equations:
  -- subsumptionₙₘ for all n, m ∈ ℕ
  -- note on solving strategy:
  -- - using β-suc-zero and β-suc-ω, suc is always pushed inside the ordinal representation
  -- - then the distributivity and the subsumption laws can be applied

-- this can be useful when working with explicit reduction (i.e. using the equalities above)
cast : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≡ ℓ₂ → Set ℓ₁ → Set ℓ₂ 
cast refl A = A