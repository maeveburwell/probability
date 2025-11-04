import Probability.Finprob

section Indicator

/-- Boolean indicator function -/
def indicator (cond : Bool) : ℚ := cond.rec 0 1

abbrev 𝕀 : Bool → ℚ := indicator

/-- Indicator is 0 or 1 -/
theorem ind_zero_one (cond : τ → Bool) : ( (𝕀∘cond) ω = 1) ∨ ((𝕀∘cond) ω = 0) := by
    by_cases h : cond ω
    · left; simp only [Function.comp_apply, h, indicator]
    · right; simp only [Function.comp_apply, h, indicator]

end Indicator


section RandomVariable

/--  Random variable defined on a finite probability space (bijection to ℕ) -/

def FinRV (ρ : Type) := ℕ → ρ


namespace FinRV
@[simp]
def and (B : FinRV Bool) (C : FinRV Bool) : FinRV Bool :=
    fun ω ↦ B ω && C ω

infix:35 " ∧ᵣ " => FinRV.and

@[simp]
def or (B : FinRV Bool) (C : FinRV Bool) : FinRV Bool :=
    fun ω ↦ B ω || C ω

infix:30 " ∨ᵣ " => FinRV.or

@[simp]
def not (B : FinRV Bool) : FinRV Bool :=
  fun ω ↦ (B ω).not

prefix:40 "¬ᵣ" => FinRV.not


@[simp]
def eq {η : Type} [DecidableEq η] (Y : FinRV η) (y : η) : FinRV Bool :=
  (fun ω ↦ decide (Y ω = y) )

infix:50 "=ᵣ" => FinRV.eq

@[simp]
def leq {η : Type} [LE η] [DecidableLE η] (Y : FinRV η) (y : η) : FinRV Bool :=
  (fun ω ↦ Y ω ≤ y)

infix:50 "≤ᵣ" => FinRV.leq

/-- Shows equivalence when extending the random variable to another element. -/
theorem le_of_le_eq (D : FinRV ℕ) (n : ℕ) : ((D ≤ᵣ n) ∨ᵣ (D =ᵣ n.succ)) = (D ≤ᵣ n.succ) := by
  funext x --extensionality principle for functions
  unfold FinRV.leq FinRV.eq FinRV.or
  grind only [cases Or]

end FinRV
