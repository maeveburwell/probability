import Probability.Probability.Basic

namespace Risk

open Findist FinRV

variable {n : ℕ}

def cdf (P : Findist n) (X : FinRV n ℚ) (t : ℚ) : ℚ := ℙ[X ≤ᵣ t // P]

variable {P : Findist n} {X Y : FinRV n ℚ} {t t₁ t₂ : ℚ}


/-- shows CDF is non-decreasing -/
theorem cdf_nondecreasing : t₁ ≤ t₂ → cdf P X t₁ ≤ cdf P X t₂ := by
  intro ht; unfold cdf
  exact exp_monotone <| rvle_monotone (le_refl X) ht


/-- Shows CDF is monotone in random variable  -/
theorem cdf_monotone_xy : X ≤ Y → cdf P X t ≥ cdf P Y t := by
  intro h; unfold cdf
  exact exp_monotone <| rvle_monotone h (le_refl t)

/-- Finite set of values taken by a random variable X : Fin n → ℚ. -/
def range (X : FinRV n ℚ) : Finset ℚ := Finset.univ.image X

--def FinQuantile (P : Findist n) (X : FinRV n ℚ) (α : ℚ) : ℚ :=

-- TODO: consider also this: 
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Stieltjes.html#StieltjesFunction.toFun

-- TODO: should we call this FinVaR? and show it is equal to a more standard definition of VaR
/-- Value-at-Risk of X at level α: VaR_α(X) = min { t ∈ X(Ω) | P[X ≤ t] ≥ α }.
If we assume 0 ≤ α ∧ α ≤ 1, then the "else 0" branch is never used. -/
def VaR (P : Findist n) (X : FinRV n ℚ) (α : ℚ) : ℚ :=
  let S : Finset ℚ := (range X).filter (fun t => cdf P X t ≥ α)
  if h : S.Nonempty then
    S.min' h
  else
    0 --this is illegal i know -- Keith can fix it :)

-- TODO: Show that VaR is a left (or right?) inverse for CDF

notation "VaR[" X "//" P ", " α "]" => VaR P X α

theorem VaR_monotone (P : Findist n) (X Y : FinRV n ℚ) (α : ℚ)
  (hXY : X ≤ Y) : VaR P X α ≤ VaR P Y α := by

  sorry


------------------Caleb's definition of VaR------------------------
theorem min_subset (A B : Finset ℕ) (h : B ⊆ A) (hA : A.Nonempty) (hB : B.Nonempty)  : A.min' hA ≤ B.min' hB :=
  by
    have hminB : B.min' hB ∈ B := Finset.min'_mem B hB
    have hminA : B.min' hB ∈ A := h hminB
    exact Finset.min'_le A (B.min' hB) hminA

def prodDenomRV (X : FinRV n ℚ) : ℕ := ∏ q ∈ range X, q.den


def X' (X : FinRV n ℚ) : FinRV n ℚ :=
  fun ω => X ω * (prodDenomRV X : ℚ)

theorem RV_QtoZ (X : FinRV n ℚ) (ω : Fin n) :
  ∃ z : ℤ, X ω * (prodDenomRV X : ℚ) = (z : ℚ) := sorry

def X'_num (X : FinRV n ℚ) : FinRV n ℤ :=
  fun ω => (X ω * (prodDenomRV X : ℚ)).num

theorem X'_num_inQ (X : FinRV n ℚ) (ω : Fin n) :
  X ω * (prodDenomRV X : ℚ) = (X'_num X ω : ℚ) := sorry


def Lx (P : Findist n) (X : FinRV n ℚ) (α : ℚ) : Finset ℚ :=
  (range X).filter (fun t => cdf P X t ≤ (1 : ℚ) - α)

theorem Lx_nonempty (P : Findist n) (X : FinRV n ℚ) (α : ℚ) :
  (Lx P X α).Nonempty := sorry

def min_Lx (P : Findist n) (X : FinRV n ℚ) (α : ℚ) :=
  (Lx P X α).min' (Lx_nonempty P X α)

--Caleb has a handwritten proof showing this definition is equivalent
def VaR_caleb (P : Findist n) (X : FinRV n ℚ) (α : ℚ) : ℚ :=
  (min_Lx P X α) / prodDenomRV X



theorem VaR_caleb_monotone (P : Findist n) (X Y : FinRV n ℚ) (α : ℚ)
  (hXY : X ≤ Y) : VaR_caleb P X α ≤ VaR_caleb P Y α := by
  sorry

------------------------------------------------------------------------




--(Emily) I am now thinking of just trying to keep it in Q
--so I wouln't use anything between these lines!
------------------- defined over the reals to prove monotonicity ---------------------------
noncomputable def cdfR (P : Findist n) (X : FinRV n ℝ) (t : ℝ) : ℝ := ℙ[X ≤ᵣ t // P]

theorem cdfR_monotone (P : Findist n) (X : FinRV n ℝ) (t1 t2 : ℝ)
  (ht : t1 ≤ t2) : cdfR P X t1 ≤ cdfR P X t2 := by
  simp [cdfR]
  apply exp_monotone
  intro ω
  by_cases h1 : X ω ≤ t1
  · have h2 : X ω ≤ t2 := le_trans h1 ht
    simp [FinRV.leq, 𝕀, indicator, h1, h2]
  · simp [𝕀, indicator, FinRV.leq, h1]
    by_cases h2 : X ω ≤ t2
    repeat simp [h2]

/-- Value-at-Risk of X at level α: VaR_α(X) = inf {t:ℝ | P[X ≤ t] ≥ α } -/
noncomputable def VaR_R (P : Findist n) (X : FinRV n ℝ) (α : ℝ) : ℝ :=
  sInf { t : ℝ | cdfR P X t ≥ α }

theorem VaR_R_monotone (P : Findist n) (X Y : FinRV n ℝ) (α : ℝ)
  (hXY : ∀ ω, X ω ≤ Y ω) : VaR_R P X α ≤ VaR_R P Y α := by
  let Sx : Set ℝ := { t : ℝ | cdfR P X t ≥ α }
  let Sy : Set ℝ := { t : ℝ | cdfR P Y t ≥ α }
  have hx : VaR_R P X α = sInf Sx := rfl
  have hy : VaR_R P Y α = sInf Sy := rfl
  have hsubset : Sy ⊆ Sx := by
    unfold Sy Sx
    intro t ht
    have h_cdf : ∀ t, cdfR P X t ≥ cdfR P Y t := by
      intro t
      unfold cdfR
      --apply exp_monotone

      sorry
    sorry
  rw [hx, hy]
  sorry

-------------------------------------------------------------------

theorem VaR_translation_invariant (P : Findist n) (X : FinRV n ℚ) (α c : ℚ) :
  VaR P (fun ω => X ω + c) α = VaR P X α + c := sorry

theorem VaR_positive_homog (P : Findist n) (X : FinRV n ℚ) (α c : ℚ)
  (hc : c > 0) : VaR P (fun ω => c * X ω) α = c * VaR P X α := sorry


/-- Tail indicator: 1 if X(ω) > t, else 0. -/
def tailInd (X : FinRV n ℚ) (t : ℚ) : FinRV n ℚ :=
  fun ω => if X ω > t then 1 else 0

/-- Conditional Value-at-Risk (CVaR) of X at level α under P.
CVaR_α(X) =  E[X * I[X > VaR] ] / P[X > VaR]
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

-- NOTE (Marek): The CVaR, as defined above is not convex/concave.
-- See Page 14 at https://www.cs.unh.edu/~mpetrik/pub/tutorials/risk2/dlrl2023.pdf
-- NOTE (Marek): The CVaR above is defined for costs and not rewards

notation "CVaR[" X "//" P ", " α "]" => CVaR P X α

--TODO: prove...
-- monotonicity: (∀ ω, X ω ≤ Y ω) → CVaR[α, X // P] ≤ CVaR[α, Y // P]
-- translation: CVaR[α, (fun ω => X ω + c) // P] = CVaR[α, X // P] + c
-- positive homogeneity: c > 0 → CVaR[α, (fun ω => c * X ω) // P] = c * CVaR[α, X // P]
-- convexity
-- CVaR ≥ VaR: CVaR[α, X // P] ≥ VaR[α, X // P]


end Risk

--- ************************* Another approach (Marek) ****************************************************

section Risk2

variable {n : ℕ} {P : Findist n} {X Y : FinRV n ℚ} {t : ℚ} 

theorem rv_le_compl_gt : (X ≤ᵣ t) + (X >ᵣ t) = 1 := by 
  ext ω
  unfold FinRV.leq FinRV.gt 
  simp 
  grind  


theorem prob_le_compl_gt : ℙ[X ≤ᵣ t // P] + ℙ[X >ᵣ t // P]= 1 := by 
  rewrite [prob_eq_exp_ind, prob_eq_exp_ind, ←exp_additive]

variable {n : ℕ} (P : Findist n) (X Y : FinRV n ℚ) (α : ℚ) (q v : ℚ) 

  

/-- Checks if the function is a quantile --/
def is_𝕢  : Prop := ℙ[ X ≤ᵣ q // P ] ≥ α ∧ ℙ[ X ≥ᵣ q // P] ≥ 1-α

/-- Set of quantiles at a level α  --/
def 𝕢Set : Set ℚ := { q | is_𝕢 P X α q}

def is_VaR : Prop := (v ∈ 𝕢Set P X α) ∧ ∀u ∈ 𝕢Set P X α, v ≥ u

theorem var_def : is_VaR P X α v ↔ (α ≥ ℙ[X <ᵣ v // P] ∧ α < ℙ[ X ≤ᵣ v // P]  ) := sorry

end Risk2
