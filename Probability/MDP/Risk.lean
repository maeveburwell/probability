import Probability.Probability.Basic

namespace Risk

open Findist FinRV

variable {n : ℕ}

def cdf (P : Findist n) (X : FinRV n ℚ) (t : ℚ) : ℚ := ℙ[X ≤ᵣ t // P]

/-- Finite set of values taken by a random variable `X : Fin n → ℚ`. -/
def rangeOfRV (X : FinRV n ℚ) : Finset ℚ := Finset.univ.image X

/-- Value-at-Risk of `X` at level `α`: `VaR_α(X) = min { t ∈ X(Ω) | P[X ≤ t] ≥ α }`.
If we assume `0 ≤ α ∧ α ≤ 1`, then the "else 0" branch is never used. -/

def VaR (P : Findist n) (X : FinRV n ℚ) (α : ℚ) : ℚ :=
  let S : Finset ℚ := (rangeOfRV X).filter (fun t => cdf P X t ≥ α)
  if h : S.Nonempty then
    S.min' h
  else
    0

notation "VaR[" α "," X "//" P "]" => VaR P X α

--TODO: prove...
--monotonicity: X ≤ Y → VaR[α, X // P] ≤ VaR[α, Y // P]
--translation: VaR[α, X + const // P] = VaR[α, X // P] + const
--positive homog: VaR[α, c • X // P] = c * VaR[α, X // P]  for c > 0


end Risk
