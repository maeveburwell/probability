import Probability.Probability.Basic
import Mathlib.Data.EReal.Basic 
import Mathlib.Data.Set.Operations

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


example (A B : Set EReal) (h : A ⊆ B) : sSup A ≤ sSup B := sSup_le_sSup h

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



end Risk

--- ************************* Another approach (Marek) ****************************************************

section Risk2

#check Set.preimage
#synth SupSet EReal 
#synth SupSet (WithTop ℝ)
#check instSupSetEReal
#check WithTop.instSupSet

variable {n : ℕ} {P : Findist n} {X Y : FinRV n ℚ} {t : ℚ} 

--TODO: can we use isLUB

theorem rv_le_compl_gt : (X ≤ᵣ t) + (X >ᵣ t) = 1 := by 
  ext ω
  unfold FinRV.leq FinRV.gt 
  simp 
  grind  


theorem prob_le_compl_gt : ℙ[X ≤ᵣ t // P] + ℙ[X >ᵣ t // P]= 1 := by 
  sorry
  --rewrite [prob_eq_exp_ind, prob_eq_exp_ind, ←exp_additive]

variable {n : ℕ} (P : Findist n) (X Y : FinRV n ℚ) (α : ℚ) (q v : ℚ) 


/-- Checks if the function is a quantile --/
def is_𝕢  : Prop := ℙ[ X ≤ᵣ q // P ] ≥ α ∧ ℙ[ X ≥ᵣ q // P] ≥ 1-α

/-- Set of quantiles at a level α  --/
def 𝕢Set : Set ℚ := { q | is_𝕢 P X α q}

def is_VaR : Prop := (v ∈ 𝕢Set P X α) ∧ ∀u ∈ 𝕢Set P X α, v ≥ u


-- theorem prob_monotone_sharp {t₁ t₂ : ℚ} : t₁ < t₂ → ℙ[X ≥ᵣ t₂ // P] ≤ ℙ[X >ᵣ t₁ // P] := 

theorem rv_monotone_sharp {t₁ t₂ : ℚ} : t₁ < t₂ → ∀ ω, (X ≥ᵣ t₂) ω →(X >ᵣ t₁) ω   := 
    by intro h ω pre
       simp [FinRV.gt, FinRV.geq] at pre ⊢ 
       linarith 
       

-- this proves that if we have the property we also have the VaR; then all remains is 
-- to show existence which we can shows constructively by actually computing the value
theorem var_def : is_VaR P X α v ↔ (ℙ[X <ᵣ v // P] ≤ α ∧ α < ℙ[ X ≤ᵣ v // P]) := sorry

def IsRiskLevel (α : ℚ) : Prop := 0 ≤ α ∧ α < 1

def RiskLevel := { α : ℚ // IsRiskLevel α}

theorem tail_monotone (X : Fin (n.succ) → ℚ) (h : Monotone X) : Monotone (Fin.tail X) := 
    by unfold Monotone at h ⊢ 
       unfold Fin.tail 
       intro a b h2 
       exact h (Fin.succ_le_succ_iff.mpr h2)
      

/-- compute a quantile for a (partial) sorted random variable and a partial probability 
    used in the induction to eliminate points until we find one that has 
    probability greater than α -/
def quantile_srt (n : ℕ) (α : RiskLevel) (p x : Fin n.succ → ℚ) 
                 (h1 : Monotone x) (h2 : ∀ω, 0 ≤ p ω) (h3 : α.val < 1 ⬝ᵥ p) 
                 (h4 : 0 < 1 ⬝ᵥ p) : Fin n.succ := 
  match n with 
  | Nat.zero => 0 
  | Nat.succ n' =>
    if h : p 0 ≤ α.val then  -- recursive case: keep going
      let α':= α.val - p 0 
      have bnd_α : IsRiskLevel α' := by 
        unfold IsRiskLevel; subst α'; specialize h2 0 
        constructor 
        · grw [←h]; simp 
        · grw [←h2]; simpa using α.2.2 
      have h': α' < 1 ⬝ᵥ (Fin.tail p) := by 
        unfold Fin.tail; subst α'
        rw [one_dotProduct] at ⊢ h3
        calc α.val - p 0 < ∑ i, p i - p 0 := by linarith  
        _  =  (p 0 + ∑ i : Fin n'.succ, p i.succ) - p 0 := by rw [Fin.sum_univ_succ]
          _ = ∑ i : Fin n'.succ, p i.succ := by ring
      Fin.succ <| quantile_srt n' ⟨α', bnd_α⟩ 
        (Fin.tail p) (Fin.tail x) (tail_monotone x h1) (fun ω ↦ h2 ω.succ) h' sorry 
    else -- return the value case
      0 

theorem quant_less {α : RiskLevel} {i : ℕ} {p x : Fin n.succ → ℚ} 
  (h1 : Monotone x) (h2 : ∀ω, 0 ≤ p ω) (h3 : α.val < 1 ⬝ᵥ p) 
        (h4 : 0 < 1 ⬝ᵥ p) (h5 : k = quantile_srt n α p x h1 h2 h3 h4) : 
          (∑ i ∈ Finset.Ico 0 k, p i ≤ α.val) ∧ ( ∑ i ∈ Finset.Icc 0 k, p i > α.val ) := sorry 

def FinVaR (α : RiskLevel) (P : Findist n) (X : FinRV n ℚ) : ℚ := 
    match n with 
    | Nat.zero => 0 -- this case is impossible because n > 0 for Findist 
    | Nat.succ n' =>
      let σ := Tuple.sort X 
      X <| quantile_srt n' α (P.p ∘ σ) (X ∘ σ) sorry sorry sorry sorry

end Risk2
