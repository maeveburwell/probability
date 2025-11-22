import Probability.Probability.Prelude

import Mathlib.Data.Matrix.Mul  -- dot product definitions and results
import Mathlib.Algebra.Notation.Pi.Defs -- operations on functions

--------------------------- Findist ---------------------------------------------------------------

section Findist

variable {n : ℕ}

structure Findist (n : ℕ) : Type where
    p : Fin n → ℚ
    prob : 1 ⬝ᵥ p = 1
    nneg : ∀ i, p i ≥ 0

namespace Findist

abbrev Delta : ℕ → Type := Findist
abbrev Δ : ℕ → Type := Delta


def singleton : Findist 1 :=
    {p    := ![1],
     prob := by simp [Matrix.vecHead],
     nneg := by simp}


@[simp]
def length (_ : Findist n) := n 

variable {n : ℕ} 

theorem nonempty (P : Findist n) : P.length > 0 := 
  by cases n 
     · have := P.prob; simp_all only [Matrix.dotProduct_of_isEmpty, zero_ne_one]
     · simp only [length, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]


end Findist

--#synth (OfNat (ℕ → ℕ) 1)
--#check One.toOfNat1
--#synth One (ℕ → ℕ)
--#check Pi.instOne
end Findist

--------------------------- Random Variable -------------------------------------------------------------------

-- Here we define random variables as finitely supported vectors

-- TODO: Or, better, define random variables as a Vector Space, or a Module.
-- see, for example:  https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Finiteness/Defs.html#Module.Finite
-- see also: https://github.com/leanprover-community/mathlib4/blob/8666bd82efec40b8b3a5abca02dc9b24bbdf2652/Mathlib/Data/Fin/VecNotation.lean

section RandomVariable

/-- A finite random variable  -/
abbrev FinRV (n : ℕ) (ρ : Type) := Fin n → ρ

/- construct a random variable -/
-- def rvOf {n : ℕ} {ρ : Type} (f : Fin n → ρ) := f

variable {n : ℕ} {ρ : Type}

namespace FinRV

-- for convenience define operations on bools
instance instBoolMul : Mul Bool where mul a b := Bool.and a b
instance instBoolAdd: Add Bool  where add a b := Bool.or a b
instance instBoolZero : Zero Bool where zero := false
instance instBoolOne : One Bool where one := true

@[simp] lemma bool_mul_tt : (true * true : Bool) = true := rfl
@[simp] lemma bool_mul_tf : (true * false : Bool) = false := rfl
@[simp] lemma bool_mul_ft : (false * true : Bool) = false := rfl
@[simp] lemma bool_mul_ff : (false * false : Bool) = false := rfl


variable {A B  : Bool}

@[simp]
theorem one_eq_true : (1:Bool) = true := rfl
@[simp]
theorem zero_eq_false : (0:Bool) = false := rfl

@[simp]
theorem bool_sum_or : A + B = Bool.or A B := rfl

theorem bool_prod_and : A * B = Bool.and A B := rfl

-- #synth Add (Fin n → ℚ)
-- #check Pi.instAdd

@[simp]
def not (B : FinRV n Bool) : FinRV n Bool :=
  fun ω ↦ (B ω).not

prefix:40 "¬ᵣ" => FinRV.not

@[simp]
def eq [DecidableEq ρ] (Y : FinRV n ρ) (y : ρ) : FinRV n Bool :=
  (fun ω ↦ decide (Y ω = y) )

infix:50 "=ᵣ" => FinRV.eq

@[simp]
def leq [LE ρ] [DecidableLE ρ] (Y : FinRV n ρ) (y : ρ) : FinRV n Bool :=
  (fun ω ↦ Y ω ≤ y)

infix:50 "≤ᵣ" => FinRV.leq

example (m n : ℕ) : (m < n) ∨ (m = n) ∨ (m > n) :=  Nat.lt_trichotomy m n

/-- Shows equivalence when extending the random variable to another element. -/
theorem le_of_le_eq (D : FinRV n ℕ) (m : ℕ) : ((D ≤ᵣ m) + (D =ᵣ m.succ)) = (D ≤ᵣ m.succ) := by
  funext x --extensionality principle for functions
  unfold FinRV.leq FinRV.eq instHAdd Add.add Pi.instAdd
  simp [instBoolAdd]
  have := Nat.lt_trichotomy (D x) (m+1)
  grind

/-- Defines a preimage of an RV. This is a set with a decidable membership. -/
def preimage (f : FinRV n ρ) : ρ → Set (Fin n) :=
  fun t => { m : Fin n | f m  = t}

end FinRV

/-- Boolean indicator function -/
def indicator {τ : Type} [OfNat τ 0] [OfNat τ 1] (cond : Bool) : τ  := cond.rec 0 1

abbrev 𝕀 [OfNat τ 0] [OfNat τ 1] : Bool → τ := indicator

/-- Indicator is 0 or 1 -/
theorem ind_zero_one (cond : τ → Bool) : ( (𝕀∘cond) ω = 1) ∨ ((𝕀∘cond) ω = 0) := by
    by_cases h : cond ω
    · left; simp only [Function.comp_apply, h, indicator]
    · right; simp only [Function.comp_apply, h, indicator]

end RandomVariable

------------------------------ Probability ---------------------------

namespace Pr

variable {n : ℕ} (P : Findist n) (B C : FinRV n Bool)

/-- Probability of B -/
def probability : ℚ :=  P.p ⬝ᵥ (𝕀 ∘ B)

notation "ℙ[" B "//" P "]" => probability P B

-- TODO: the sorry in the definition has to do with the decidability of the membership
--theorem prob_iprod_eq_def : ℙ[B // P] = P.measure (B.preimage true) sorry := sorry

/-- Conditional probability of B -/
def probability_cnd : ℚ := ℙ[B * C // P] / ℙ[ C // P ]

#loogle "Pi.single"

theorem one_of_true : 𝕀 ∘ (1 : Fin n → Bool) = (1 : Fin n → ℚ)  :=
  by ext
     simp [𝕀, indicator]


#synth (OfNat Bool 1)
#check One.toOfNat1


theorem true_one : ℙ[ 1 // P] = 1 :=
    by unfold probability
       rw[one_of_true]
       rw [dotProduct_comm]
       exact P.prob

---- conditional probability
notation "ℙ[" B "|" C "//" P "]" => probability_cnd P B C

end Pr

------------------------------ PMF ---------------------------

/-- Proof that p is a the PMF of X on probability space P -/
def PMF {K : ℕ} (pmf : Fin K → ℚ) (P : Findist n) (L : FinRV n (Fin K)) :=
    ∀ k : Fin K, pmf k = ℙ[ L =ᵣ k // P]

namespace PMF


end PMF

------------------------------ Expectation ----------------------

namespace Ex


variable {n : ℕ} (P : Findist n) (X Y Z: FinRV n ℚ) (B : FinRV n Bool)

def expect : ℚ := P.p ⬝ᵥ X

notation "𝔼[" X "//" P "]" => expect P X

-- expectation for a joint probability space and random variable
notation "𝔼[" PX "]" => expect PX.1 PX.2

--theorem exp_eq_correct : 𝔼[X // P] = ∑ v ∈ ((List.finRange P.length).map X).toFinset, v * ℙ[ X =ᵣ v // P]
--:= sorry


/-- Conditional expectation -/
def expect_cnd : ℚ := 𝔼[ X * (𝕀 ∘ B) // P] / ℙ[ B // P]

notation "𝔼[" X "|" B "//" P "]" => expect_cnd P X B

-- expectation for a joint probability space and random variable
notation "𝔼[" PX "|" B "]" => expect_cnd PX.1 PX.2 B

variable {K : ℕ} (L : FinRV n (Fin K))

-- creates a random variable
def expect_cnd_rv : Fin n → ℚ := fun i ↦ 𝔼[ X | L =ᵣ (L i) // P ]

notation "𝔼[" X "|ᵣ" L "//" P "]" => expect_cnd_rv P X L

end Ex
