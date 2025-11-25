import Probability.Probability.Basic

namespace Risk

open Findist FinRV

variable {n : ℕ}

def cdf (P : Findist n) (X : FinRV n ℚ) (t : ℚ) : ℚ := ℙ[X ≤ᵣ t // P]

/-- Finite set of values taken by a random variable X : Fin n → ℚ. -/
def rangeOfRV (X : FinRV n ℚ) : Finset ℚ := Finset.univ.image X

/-- Value-at-Risk of X at level α: VaR_α(X) = min { t ∈ X(Ω) | P[X ≤ t] ≥ α }.
If we assume 0 ≤ α ∧ α ≤ 1, then the "else 0" branch is never used. -/

def VaR (P : Findist n) (X : FinRV n ℚ) (α : ℚ) : ℚ :=
  let S : Finset ℚ := (rangeOfRV X).filter (fun t => cdf P X t ≥ α)
  if h : S.Nonempty then
    S.min' h
  else
    0

notation "VaR[" α "," X "//" P "]" => VaR P X α

theorem VaR_monotone (P : Findist n) (X Y : FinRV n ℚ) (α : ℚ)
  (hXY : ∀ ω, X ω ≤ Y ω) : VaR P X α ≤ VaR P Y α := by
  have hcdf : ∀ t : ℚ, cdf P X t ≤ cdf P Y t := by
    intro t
    have h_ind : (𝕀 ∘ (Y ≤ᵣ t)) ≤ (𝕀 ∘ (X ≤ᵣ t)) := by
      intro ω
      have h1 : Y ω ≤ t → X ω ≤ t := by
        intro hY
        exact le_trans (hXY ω) hY
      by_cases hY : Y ω ≤ t
      · have hX : X ω ≤ t := by exact h1 hY
        simp [𝕀, indicator, FinRV.leq, hY, hX]
      · simp [𝕀, indicator, FinRV.leq, hY]
    simp [cdf]

    sorry
  sorry

theorem VaR_translation_invariant (P : Findist n) (X : FinRV n ℚ) (α c : ℚ) :
  VaR P (fun ω => X ω + c) α = VaR P X α + c := sorry

theorem VaR_positive_homog (P : Findist n) (X : FinRV n ℚ) (α c : ℚ)
  (hc : c > 0) : VaR P (fun ω => c * X ω) α = c * VaR P X α := sorry


/-- Tail indicator: 1 if X(ω) > t, else 0. -/
def tailInd (X : FinRV n ℚ) (t : ℚ) : FinRV n ℚ :=
  fun ω => if X ω > t then 1 else 0

/-- Conditional Value-at-Risk (CVaR) of X at level α under P.
CVaR =  E[X * I[X > VaR] ] / P[X > VaR]
If the tail probability is zero, CVaR is defined to be 0.
-/
def CVaR (P : Findist n) (X : FinRV n ℚ) (α : ℚ) : ℚ :=
  let v := VaR P X α
  let B : FinRV n ℚ := tailInd X v
  let num := 𝔼[X * B // P]
  let den := ℙ[X >ᵣ v // P]
  if _ : den = 0 then
     0
  else
     num / den

notation "CVaR[" α "," X "//" P "]" => CVaR P X α

--TODO: prove...
-- monotonicity: (∀ ω, X ω ≤ Y ω) → CVaR[α, X // P] ≤ CVaR[α, Y // P]
-- translation: CVaR[α, (fun ω => X ω + c) // P] = CVaR[α, X // P] + c
-- positive homogeneity: c > 0 → CVaR[α, (fun ω => c * X ω) // P] = c * CVaR[α, X // P]
-- convexity
-- CVaR ≥ VaR: CVaR[α, X // P] ≥ VaR[α, X // P]

end Risk
