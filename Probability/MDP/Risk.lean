import Probability.Probability.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Set.Operations

namespace Risk

open Findist FinRV

variable {n : ℕ}

--TODO: many of the basic results below belong to Probability.Defs or Probability.Basic

def cdf (P : Findist n) (X : FinRV n ℚ) (t : ℚ) : ℚ := ℙ[X ≤ᵣ t // P]

variable {P : Findist n} {X Y : FinRV n ℚ} {t t₁ t₂ : ℚ}

theorem false_of_le_gt {x y : ℚ} : x ≤ y → x > y → False :=
    by intro h1 h2; grw [h1] at h2; exact (lt_self_iff_false y).mp h2

theorem false_of_lt_ge {x y : ℚ} : x < y → x ≥ y → False :=
    fun h1 h2 => false_of_le_gt h2 h1 

/-- shows CDF is non-decreasing -/
theorem cdf_nondecreasing : t₁ ≤ t₂ → cdf P X t₁ ≤ cdf P X t₂ := by
  intro ht; unfold cdf
  apply prob_le_monotone (le_refl X) ht

/-- Shows CDF is monotone in random variable  -/
theorem cdf_monotone_xy : X ≤ Y → cdf P X t ≥ cdf P Y t := by
  intro h; unfold cdf
  apply prob_le_monotone h (le_refl t)

variable {β : Type}

theorem rv_image_nonempty  [DecidableEq β] [LinearOrder β] (P : Findist n) (X : FinRV n β)  :
    (Finset.univ.image X).Nonempty :=
  match n with
  | Nat.zero => P.nonempty' |> False.elim
  | Nat.succ _ => Finset.image_nonempty.mpr Finset.univ_nonempty

def FinRV.min [DecidableEq β] [LinearOrder β] (P : Findist n) (X : FinRV n β) : β :=
  (Finset.univ.image X).min' (rv_image_nonempty P X)

def FinRV.max [DecidableEq β] [LinearOrder β] (P : Findist n) (X : FinRV n β) : β :=
  (Finset.univ.image X).max' (rv_image_nonempty P X)

variable {X : FinRV n ℚ}

theorem rv_omega_le_max (P : Findist n) : ∀ω, X ω ≤ (FinRV.max P X) :=
    by intro ω
       have h : X ω ∈ (Finset.image X Finset.univ) := Finset.mem_image_of_mem X (Finset.mem_univ ω)
       simpa using Finset.le_max' (Finset.image X Finset.univ) (X ω) h

theorem rv_le_max_one : (X ≤ᵣ (FinRV.max P X)) = 1 :=
    by ext ω
       unfold FinRV.leq FinRV.max
       simpa using rv_omega_le_max P ω

theorem rv_max_in_image : (FinRV.max P X) ∈ Finset.univ.image X :=
    by unfold FinRV.max
       exact Finset.max'_mem (Finset.image X Finset.univ) (rv_image_nonempty P X)

theorem prob_le_eq_one : ℙ[X ≤ᵣ (FinRV.max P X) // P] = 1 := by rw [rv_le_max_one]; exact prob_one_of_true P

theorem rv_omega_ge_min (P : Findist n) : ∀ω, X ω ≥ (FinRV.min P X) :=
    by intro ω
       have h : X ω ∈ (Finset.image X Finset.univ) := Finset.mem_image_of_mem X (Finset.mem_univ ω)
       simpa using Finset.min'_le (Finset.image X Finset.univ) (X ω) h

theorem rv_ge_min_one : (X ≥ᵣ (FinRV.min P X)) = 1 :=
    by ext ω
       unfold FinRV.geq FinRV.min
       simpa using rv_omega_ge_min P ω

theorem prob_ge_eq_one : ℙ[X ≥ᵣ (FinRV.min P X) // P] = 1 := by rw [rv_ge_min_one]; exact prob_one_of_true P

theorem prob_lt_min_eq_zero : ℙ[X <ᵣ (FinRV.min P X) // P] = 0 := by
    rw [prob_lt_of_ge, prob_ge_eq_one]; exact sub_self 1

section rounding_existence

variable (P : Findist n) (X : FinRV n ℚ) (t : ℚ)

-- TODO: this requires the condition that: t < (FinRV.max P X)

theorem rv_ge_lt_mem_of_lt : ∃q ≥ t, (X <ᵣ q) = (X <ᵣ t) ∧ q ∈ (Finset.univ.image X) := sorry 

theorem prob_ge_lt_mem_of_lt : ∃q ≥ t, ℙ[X <ᵣ q // P] = ℙ[X <ᵣ t // P] ∧ q ∈ (Finset.univ.image X) := by 
    obtain ⟨q, hq ⟩ := rv_ge_lt_mem_of_lt X t
    use q 
    constructor
    · exact hq.1 
    · constructor 
      · exact congrArg (probability P) hq.2.1
      · exact hq.2.2

theorem rv_lt_epsi_eq_le_of_lt : t < (FinRV.max P X) → ∃q > t, (X <ᵣ q) = (X ≤ᵣ t) ∧ q ∈ (Finset.univ.image X) :=
    by intro h0
       let 𝓧 := Finset.univ.image X
       let 𝓨 := 𝓧.filter (fun x ↦ x > t)
       have h : 𝓨.Nonempty := Finset.filter_nonempty_iff.mpr ⟨FinRV.max P X, ⟨rv_max_in_image, h0⟩⟩
       let y := 𝓨.min' h
       have hy1 : y ∈ 𝓨 := Finset.min'_mem 𝓨 h
       have hy2 : y ∈ 𝓧 ∧ y > t := Finset.mem_filter.mp hy1
       use y
       constructor
       · by_contra! le
         exact false_of_le_gt le hy2.2
       · constructor
         · unfold FinRV.leq FinRV.lt
           ext ω
           rw [decide_eq_decide]
           constructor
           · intro h2
             have xωx : X ω ∈ 𝓧 := Finset.mem_image_of_mem X (Finset.mem_univ ω)
             have hxω : X ω ∉ 𝓨 := by
                by_contra! inY
                have : y ≤ X ω := Finset.min'_le 𝓨 (X ω) inY
                exact false_of_le_gt this h2
             rw [Finset.mem_filter] at hxω
             push_neg at hxω
             exact hxω xωx
           · intro h2
             grewrite [h2]
             exact hy2.2
         · exact Finset.mem_of_mem_filter y hy1

theorem prob_lt_epsi_eq_le_of_lt : t < (FinRV.max P X) →
          ∃q > t, ℙ[X <ᵣ q // P] = ℙ[X ≤ᵣ t // P] ∧ q ∈ (Finset.univ.image X) :=
      fun h => let ⟨q, hq⟩ := rv_lt_epsi_eq_le_of_lt P X t h
      Exists.intro q ⟨hq.1, ⟨ congrArg (probability P) hq.2.1, hq.2.2 ⟩⟩

-- for discrete random variables
theorem rv_lt_epsi_eq_le (P : Findist n) : ∃q > t, (X <ᵣ q) = (X ≤ᵣ t) :=
       let 𝓧 := Finset.univ.image X
       let 𝓨 := 𝓧.filter (fun x ↦ x > t)
       by cases' lt_or_ge t (FinRV.max P X) with hlt hge
          · obtain ⟨q, h⟩ := rv_lt_epsi_eq_le_of_lt P X t hlt
            exact ⟨q, ⟨h.1, h.2.1⟩⟩
          · have h := rv_omega_le_max P (X:=X)
            grw [hge] at h
            let q := t + 1
            have b : ∀ω, X ω < q := fun ω => lt_add_of_le_of_pos (h ω) rfl
            have ab : (X <ᵣ q) = (X ≤ᵣ t) := by
                ext ω; unfold FinRV.leq FinRV.lt; grind only
            exact ⟨q, ⟨lt_add_one t, ab ⟩ ⟩

-- will follow from rv_lt_epsi_eq_lt by congruence
theorem prob_lt_epsi_eq_le : ∃q > t, ℙ[X <ᵣ q // P] = ℙ[X ≤ᵣ t // P] :=
      let ⟨q, hq⟩ := rv_lt_epsi_eq_le X t P
      Exists.intro q ⟨hq.1, congrArg (probability P) hq.2⟩

end rounding_existence

def IsRiskLevel (α : ℚ) : Prop := 0 ≤ α ∧ α < 1

def RiskLevel := { α : ℚ // IsRiskLevel α}

/-- Value-at-Risk of X at level α: VaR_α(X) = min { t ∈ X(Ω) | P[X ≤ t] ≥ α }.
    If we assume 0 ≤ α < 1, then the "else 0" branch is never used. -/
def FinVaR1 (P : Findist n) (X : FinRV n ℚ) (α : RiskLevel) : ℚ :=
  let 𝓧 := Finset.univ.image X
  let 𝓢 := 𝓧.filter (fun t ↦ ℙ[X <ᵣ t // P] ≤ α.val)
  have h : 𝓢.Nonempty := by
    apply Finset.filter_nonempty_iff.mpr
    let xmin := (Finset.univ.image X).min' (rv_image_nonempty P X)
    use xmin
    constructor
    · exact Finset.min'_mem 𝓧 (rv_image_nonempty P X)
    · have : ℙ[X <ᵣ xmin // P] = 0 := prob_lt_min_eq_zero
      have := α.2
      unfold IsRiskLevel at this
      linarith
  𝓢.max' h

variable {α : RiskLevel}

theorem var1_prob_lt_var_le_alpha : ℙ[X <ᵣ (FinVaR1 P X α) // P] ≤ α.val := by
    generalize h : (FinVaR1 P X α) = t
    unfold FinVaR1 at h
    extract_lets 𝓧 𝓢 ne𝓢 at h
    have tS : t ∈ 𝓢 := by subst h; exact Finset.max'_mem 𝓢 ne𝓢
    exact (Finset.mem_filter.mp tS).right

example : X ≤ X := le_refl X

theorem var1_prob_le_var_gt_alpha : ℙ[X ≤ᵣ (FinVaR1 P X α) // P] > α.val := by
    generalize h : (FinVaR1 P X α) = t
    unfold FinVaR1 at h
    extract_lets 𝓧 𝓢 ne𝓢 at h
    by_contra! hg
    have tlt : t < (FinRV.max P X) :=
        by by_contra!
           unfold RiskLevel IsRiskLevel at α
           have hh := prob_le_monotone (P := P) (le_refl X) this
           rw [prob_le_eq_one] at hh
           have := α.2.2
           linarith
    obtain ⟨q, hq⟩ := prob_lt_epsi_eq_le_of_lt P X t tlt
    rcases hq with ⟨hqgt, hqp, hqin⟩
    have hqs : q ∈ 𝓢 := by
      apply Finset.mem_filter.mpr
      constructor
      · exact hqin
      · rw [hqp]; exact hg
    have : q ≤ t := by subst h; exact Finset.le_max' 𝓢 q hqs
    linarith

notation "VaR[" X "//" P ", " α "]" => FinVaR1 P X α

variable {n : ℕ} (P : Findist n) (X Y : FinRV n ℚ) (α : RiskLevel) (q v : ℚ)

/-- Proof the `q` is an `α`-quantile of `X` --/
def IsQuantile  : Prop := ℙ[ X ≤ᵣ q // P ] ≥ α.val ∧ ℙ[ X ≥ᵣ q // P] ≥ 1 - α.val

/-- Proof that `q` is a lower bound on the `α`-quantile of `X` --/
def IsQuantileLower : Prop := ℙ[ X ≥ᵣ q // P] ≥ 1 - α.val

/-- Set of quantiles at a level `α`  --/
def Quantile : Set ℚ := { q | IsQuantile P X α q}

/-- Set of lower bounds on a quantile at `α` -/
def QuantileLower : Set ℚ := {q | IsQuantileLower P X α q}

/-- Value `q` is the Value at Risk at `α` of `X` and probability `P`  -/
def IsVaR : Prop := IsGreatest (Quantile P X α) v 

/-- A simpler, equivalent definition of Value at Risk  -/
def IsVaR2 : Prop := IsGreatest (QuantileLower P X α) v 

-- theorem prob_monotone_sharp {t₁ t₂ : ℚ} : t₁ < t₂ → ℙ[X ≥ᵣ t₂ // P] ≤ ℙ[X >ᵣ t₁ // P] :=

variable {n : ℕ} {P : Findist n} {X Y : FinRV n ℚ} {α : RiskLevel} {q v q₁ q₂ : ℚ}

theorem rv_monotone_sharp {t₁ t₂ : ℚ} : t₁ < t₂ → ∀ ω, (X ≥ᵣ t₂) ω →(X >ᵣ t₁) ω   :=
    by intro h ω pre
       simp [FinRV.gt, FinRV.geq] at pre ⊢
       linarith

theorem qset_lb : q ∈ Quantile P X α → ℙ[ X ≤ᵣ q // P ] ≥ α.val := by simp_all [Quantile, IsQuantile]

theorem qset_ub : q ∈ Quantile P X α → ℙ[ X ≥ᵣ q // P] ≥ 1 - α.val := by simp_all [Quantile, IsQuantile]

theorem qset_def : q ∈ Quantile P X α ↔ ℙ[ X ≤ᵣ q // P ] ≥ α.val ∧ ℙ[ X ≥ᵣ q // P] ≥ 1 - α.val := by simp_all [Quantile, IsQuantile]

theorem qset_not_def : q ∉ Quantile P X α ↔ ℙ[ X ≤ᵣ q // P ] < α.val ∨ ℙ[ X ≥ᵣ q // P] < 1 - α.val := by 
    constructor; repeat intro h2; grind [qset_def]

theorem qsetlower_def : q ∈ QuantileLower P X α ↔ ℙ[ X ≥ᵣ q // P] ≥ 1 - α.val := by simp_all [QuantileLower, IsQuantileLower]

theorem qsetlower_def_lt : q ∈ QuantileLower P X α ↔ ℙ[ X <ᵣ q // P] ≤ α.val := 
    by constructor 
       · intro h; have := qsetlower_def.mp h; rw [prob_lt_of_ge]; linarith
       · intro h; rw [prob_lt_of_ge] at h;
         suffices  ℙ[X≥ᵣq // P] ≥ 1-α.val from this   
         linarith 

theorem qset_ub_lt : q ∈ Quantile P X α → ℙ[ X <ᵣ q // P] ≤ α.val :=
  by intro h
     have := qset_ub h
     rewrite [prob_ge_of_lt] at this
     linarith

theorem qset_of_cond : ℙ[ X ≤ᵣ q // P ] ≥ α.val ∧ ℙ[ X ≥ᵣ q // P] ≥ 1 - α.val → q ∈ Quantile P X α :=
    by intro h; simp_all [Quantile, IsQuantile]

theorem qset_of_cond_lt : ℙ[ X ≤ᵣ q // P ] ≥ α.val ∧ ℙ[ X <ᵣ q // P] ≤ α.val → q ∈ Quantile P X α :=
    by intro h1
       have h2 : ℙ[ X ≥ᵣ q // P] ≥ 1 - α.val := by rw [prob_ge_of_lt]; linarith
       exact qset_of_cond ⟨h1.1, h2⟩

theorem qsetlower_of_cond : ℙ[ X ≤ᵣ q // P ] ≥ α.val ∧ ℙ[ X ≥ᵣ q // P] ≥ 1 - α.val → q ∈ QuantileLower P X α :=
    by intro h; simp_all [QuantileLower, IsQuantileLower]

theorem qsetlower_of_cond_lt : ℙ[ X ≤ᵣ q // P ] ≥ α.val ∧ ℙ[ X <ᵣ q // P] ≤ α.val → q ∈ QuantileLower P X α :=
    by intro h1
       have h2 : ℙ[ X ≥ᵣ q // P] ≥ 1 - α.val := by rw [prob_ge_of_lt]; linarith
       exact qsetlower_of_cond ⟨h1.1, h2⟩

theorem prob_lt_le_monotone : q > t → ℙ[X <ᵣ q // P] ≥ ℙ[X ≤ᵣ t // P] :=
    by intro h
       unfold probability dotProduct
       apply Finset.sum_le_sum
       intro ω hω
       have h2 : (𝕀 ∘ (X ≤ᵣ t)) ω ≤ (𝕀 ∘ (X <ᵣ q)) ω :=
         by by_cases h3 : X ω ≤ t
            · have h4 : X ω < q := lt_of_le_of_lt h3 h
              simp [FinRV.leq, FinRV.lt, 𝕀, indicator, Function.comp, h3, h4]
            · simp [𝕀, indicator, FinRV.leq, FinRV.lt, Function.comp, h3]
              by_cases h5 : X ω < q <;> simp [h5] -- <;> applies to both cases
       exact mul_le_mul_of_nonneg_left h2 (P.nneg ω)

theorem var_prob_cond : IsVaR P X α v ↔ (ℙ[X <ᵣ v // P] ≤ α.val ∧ α.val < ℙ[ X ≤ᵣ v // P]) :=
  by constructor
     · intro h
       constructor
       · unfold IsVaR Quantile IsQuantile IsGreatest at h
         have h1 : ℙ[X≥ᵣv//P] ≥ 1 - α.val := by simp_all
         rw [prob_ge_of_lt] at h1
         linarith
       · by_contra! hc
         obtain ⟨q,hq⟩ := prob_lt_epsi_eq_le P X v
         have h3 : q ∈ Quantile P X α := by
            rewrite [←hq.2] at hc
            have qlb := qset_lb h.1
            grewrite [prob_le_monotone (le_refl X) (le_of_lt hq.1)]  at qlb
            exact qset_of_cond_lt ⟨qlb, hc⟩
         unfold IsVaR IsGreatest upperBounds at h
         exact false_of_le_gt (h.2 h3) hq.1
     · intro h
       unfold IsVaR
       constructor
       · exact qset_of_cond_lt ⟨le_of_lt h.2, h.1⟩
       · unfold upperBounds
         by_contra! hc
         simp at hc
         obtain ⟨q, hq⟩ := hc
         have := qset_ub_lt hq.1
         have := prob_lt_le_monotone (P:=P) (X:=X) hq.2
         linarith

theorem var2_prob_cond : IsVaR2 P X α v ↔ (ℙ[X <ᵣ v // P] ≤ α.val ∧ α.val < ℙ[ X ≤ᵣ v // P]) :=
  by constructor
     · intro h
       constructor
       · have h1 : 1 - ℙ[X<ᵣv//P] ≥ 1 - α.val := by simp_all [IsVaR2,IsGreatest,QuantileLower,IsQuantileLower,prob_ge_of_lt]
         linarith
       · by_contra! hc
         obtain ⟨q,hq⟩ := prob_lt_epsi_eq_le P X v
         have h3 : q ∈ QuantileLower P X α := by
            rw [←hq.2,prob_lt_of_ge] at hc
            suffices ℙ[X≥ᵣq//P] ≥ 1 - α.val from this 
            linarith
         exact false_of_le_gt (h.2 h3) hq.1
     · intro h
       unfold IsVaR2
       constructor
       · exact qsetlower_of_cond_lt ⟨le_of_lt h.2, h.1⟩
       · unfold upperBounds
         by_contra! hc
         simp at hc
         obtain ⟨q, hq⟩ := hc
         have hu : ℙ[X ≤ᵣ v // P] ≤ α.val := 
            calc ℙ[X ≤ᵣ v // P] ≤  ℙ[X <ᵣ q // P] := prob_lt_le_monotone hq.2
                 _ ≤ α.val := qsetlower_def_lt.mp hq.1  
         exact false_of_lt_ge h.2 hu 

-- This is the main correctness proof
theorem finvar1_correct : IsVaR P X α (FinVaR1 P X α) :=
    by rewrite[var_prob_cond]; exact ⟨var1_prob_lt_var_le_alpha, var1_prob_le_var_gt_alpha⟩

theorem var_is_quantile : IsVaR P X α v → IsQuantile P X α v := 
    fun h => by simp_all only [Set.mem_setOf_eq,IsVaR,Quantile,IsGreatest]

theorem var_is_quantilelower : IsVaR P X α v → IsQuantileLower P X α v := 
    fun h => by simp_all only [Set.mem_setOf_eq,IsVaR,Quantile,IsGreatest,IsQuantileLower,IsQuantile]


theorem var2_is_quantilelower : IsVaR2 P X α v → IsQuantileLower P X α v := 
    fun h => by simp_all only [Set.mem_setOf_eq,IsVaR2,QuantileLower,IsGreatest,Set.mem_setOf_eq]

theorem quantile_implies_quantilelower : IsQuantile P X α v → IsQuantileLower P X α v := 
    by simp[IsQuantile, IsQuantileLower]

theorem quantile_nonempty : (Quantile P X α).Nonempty := 
  Set.nonempty_def.mpr ⟨ VaR[X// P,α], finvar1_correct  |> var_is_quantile ⟩

theorem quantile_subset_quantilelower : Quantile P X α ⊆ QuantileLower P X α := fun _ => quantile_implies_quantilelower

theorem isquantilelower_le_isquantile : IsCofinalFor (QuantileLower P X α) (Quantile P X α) := by 
    intro q₁ h 
    by_cases h2 : q₁ ∈ Quantile P X α
    · exact ⟨q₁, h2, le_refl q₁⟩
    · rewrite [qset_not_def] at h2
      rewrite [qsetlower_def] at h 
      cases' h2 with h2l h2r
      · obtain ⟨q₂, hq₂⟩ : (Quantile P X α).Nonempty := quantile_nonempty
        use q₂
        constructor 
        · exact hq₂
        · by_contra! ine
          exact ge_trans (prob_le_monotone (le_refl X) (le_of_lt ine)) (qset_lb hq₂) |> false_of_lt_ge h2l 
      · exfalso; exact false_of_lt_ge h2r h 

theorem isquantile_le_isquantilelower : IsCofinalFor (Quantile P X α) (QuantileLower P X α) := 
    HasSubset.Subset.iscofinalfor quantile_subset_quantilelower

theorem var2_is_quantile : IsVaR2 P X α v → IsQuantile P X α v := by 
    intro h 
    constructor
    · suffices ℙ[X≤ᵣv//P] > α.val by linarith
      exact (var2_prob_cond.mp h).2
    · exact var2_is_quantilelower h


theorem var_eq_var2 : IsVaR P X α v ↔ IsVaR2 P X α v := by
    constructor 
    · intro h 
      constructor 
      · exact var_is_quantilelower h 
      · exact (upperBounds_mono_of_isCofinalFor isquantilelower_le_isquantile) h.2
    · intro h 
      constructor 
      · exact var2_is_quantile h  
      · exact (upperBounds_mono_of_isCofinalFor isquantile_le_isquantilelower) h.2

----------------------------- Fast VaR computation -------------------------------------------------------

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
      let αval':= α.val - p 0
      have bnd_α : IsRiskLevel (α.val - p 0) := by
        unfold IsRiskLevel; subst αval'; specialize h2 0
        constructor
        · grw [←h]; simp
        · grw [←h2]; simpa using α.2.2
      let α' := ⟨αval', bnd_α⟩
      let h1' := (tail_monotone x h1)
      let h2' := (fun ω : Fin n'.succ ↦ h2 ω.succ)
      let h3': αval' < 1 ⬝ᵥ (Fin.tail p) := by
        unfold Fin.tail; subst αval'
        rw [one_dotProduct] at ⊢ h3
        calc α.val - p 0 < ∑ i, p i - p 0 := by linarith
          _  =  (p 0 + ∑ i : Fin n'.succ, p i.succ) - p 0 := by rw [Fin.sum_univ_succ]
          _ = ∑ i : Fin n'.succ, p i.succ := by ring
      let h4' := (lt_of_le_of_lt bnd_α.left h3')
      Fin.succ <| quantile_srt n' α' (Fin.tail p) (Fin.tail x) h1' h2' h3' h4'
    else -- return the value case: p 0 > α
      0

example {p : Fin n.succ → ℚ} : ∑ i ∈ Finset.Icc (0 : Fin n.succ) k, p i = (∑ i ∈ Finset.Ico (0: Fin n.succ) k, p i) + p k
     := sorry

theorem quant_less (n : ℕ) {k : Fin n.succ} (α : RiskLevel) (p x : Fin n.succ → ℚ)
      (h1 : Monotone x) (h2 : ∀ω, 0 ≤ p ω) (h3 : α.val < 1 ⬝ᵥ p)
      (h4 : 0 < 1 ⬝ᵥ p) (h5 : k = quantile_srt n α p x h1 h2 h3 h4) :
      (∑ i ∈ Finset.Ico 0 k, p i ≤ α.val) ∧ ( ∑ i ∈ Finset.Icc 0 k, p i > α.val ) := by
        subst h5
        induction n generalizing α with
        | zero =>
          constructor
          · have h6 : 0 ≤ α.val := α.property.left
            simp [h6]
          · have h7 : (α.val : ℚ) < p 0 := by
              rw [one_dotProduct] at h3
              simpa [Fin.sum_univ_succ] using h3
            simpa [quantile_srt] using h7
        | succ n ih =>
          by_cases h8 : p 0 ≤ α.val
          · unfold quantile_srt
            split_ifs
            · extract_lets αval' _ α' h1' h2' h3' h4'
              specialize ih α' (Fin.tail p) (Fin.tail x) h1' h2' h3' h4'
              simp_all
              constructor
              · sorry
              · sorry
            · contradiction
            --simp [h8]
          · have h9 : p 0 > α.val := lt_of_not_ge h8
            constructor
            · have h0 : 0 ≤ α.val := α.property.left
              simp [quantile_srt, h8, h0]
            · simpa [quantile_srt, h8] using h9


def FinVaR (α : RiskLevel) (P : Findist n) (X : FinRV n ℚ) : ℚ :=
    match n with
    | Nat.zero => 0 -- this case is impossible because n > 0 for Findist
    | Nat.succ n' =>
      let σ := Tuple.sort X
      X <| quantile_srt n' α (P.p ∘ σ) (X ∘ σ)
      (Tuple.monotone_sort X)
      (by intro ω; simpa [Function.comp] using P.nneg (σ ω))
      --h3 : α.val < 1 ⬝ᵥ p
      (by
        have h1 : (1 : Fin (Nat.succ n') → ℚ) ∘ σ ⬝ᵥ P.p ∘ σ = 1 ⬝ᵥ P.p :=
          comp_equiv_dotProduct_comp_equiv (1 : Fin (Nat.succ n') → ℚ) P.p σ
        have h2 : ((1 : Fin (Nat.succ n') → ℚ) ∘ σ) = 1 := by
          funext i
          simp [Function.comp]
        have h3 : (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ P.p := by
          simpa [h2] using h1
        have h4 : (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = 1 := by
          calc
            (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ P.p := h3
            _ = 1 := P.prob
        simpa [h4] using (α.property).right)
      --h4 : 0 < 1 ⬝ᵥ p
      ----this is all the same except for the last line
      ----is there a way to avoid repeating it???
      (by
        have h1 : (1 : Fin (Nat.succ n') → ℚ) ∘ σ ⬝ᵥ P.p ∘ σ = 1 ⬝ᵥ P.p :=
          comp_equiv_dotProduct_comp_equiv (1 : Fin (Nat.succ n') → ℚ) P.p σ
        have h2 : ((1 : Fin (Nat.succ n') → ℚ) ∘ σ) = 1 := by
          funext i
          simp [Function.comp]
        have h3 : (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ P.p := by
          simpa [h2] using h1
        have h4 : (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = 1 := by
          calc
            (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ (P.p ∘ σ) = (1 : Fin (Nat.succ n') → ℚ) ⬝ᵥ P.p := h3
            _ = 1 := P.prob
        simp [h4])


-------------------- VaR Properties -----------------------------------------------------------------------------


section VaR_properties

variable {P : Findist n} {X Y : FinRV n ℚ} {q q₁ v₁ v₂ c : ℚ} {α : RiskLevel}

--(IsQuantileLower P X α q₁) → ∃q₂ ≥ q₁, IsQuantileLower P Y α q₂ := by 
theorem quantile_le_monotone : X ≤ Y → IsCofinalFor (QuantileLower P X α) (IsQuantileLower P Y α) := by
  intro hle q₁ hvar₁
  have hq₁ := le_refl q₁
  exact ⟨q₁, ⟨le_trans hvar₁ (prob_ge_antitone hle hq₁), hq₁⟩⟩
    
theorem var2_monotone : X ≤ Y → IsVaR2 P X α v₁ → IsVaR2 P Y α v₂ → v₁ ≤ v₂ := 
  fun hle hv1 hv2 => upperBounds_mono_of_isCofinalFor (quantile_le_monotone hle) hv2.2 hv1.1 


--- some probablity interlude that will need to be moved ---------------------

variable {c x : ℚ}

theorem rv_le_cashinvar (c:ℚ): (X ≤ᵣ x) = (X + c•1 ≤ᵣ x + c) := by ext ω; simp 

theorem prob_le_cashinvar (c:ℚ) : ℙ[X ≤ᵣ x // P] = ℙ[X + c•1 ≤ᵣ x + c // P] := congrArg (probability P) (rv_le_cashinvar c)

theorem rv_lt_cashinvar (c:ℚ) : (X <ᵣ x) = (X + c•1 <ᵣ x + c) := by ext ω; simp 

theorem prob_lt_cashinvar (c:ℚ) : ℙ[X <ᵣ x // P] = ℙ[X + c•1 <ᵣ x + c // P] := congrArg (probability P) (rv_lt_cashinvar c)

theorem rv_ge_cashinvar (c:ℚ) : (X ≥ᵣ x) = (X + c•1 ≥ᵣ x + c) := by ext ω; simp 

theorem prob_ge_cashinvar (c:ℚ) : ℙ[X ≥ᵣ x // P] = ℙ[X + c•1 ≥ᵣ x + c // P] := congrArg (probability P) (rv_ge_cashinvar c)

theorem rv_gt_cashinvar (c:ℚ) : (X >ᵣ x) = (X + c•1 >ᵣ x + c) := by ext ω; simp 

theorem prob_gt_cashinvar (c:ℚ) : ℙ[X >ᵣ x // P] = ℙ[X + c•1 >ᵣ x + c // P] := congrArg (probability P) (rv_gt_cashinvar c)

--- end probability interlude

theorem quantilelower_cashinv : q ∈ QuantileLower P X α ↔ (q+c) ∈ QuantileLower P (X+c•1) α := by 
  constructor
  · intro h; rw [qsetlower_def, prob_ge_cashinvar c] at h; exact h 
  · intro h; rw [qsetlower_def, prob_ge_cashinvar c]; exact h 

theorem quantilelower_cash_image : QuantileLower P (X+c•1) α = (fun x ↦ x+c) '' QuantileLower P X α := by 
  apply Set.eq_of_subset_of_subset
  · unfold Set.image
    intro qc hqc
    --rw [quantilelower_cashinv (c:=c)] at hq
    use qc-c 
    constructor 
    · generalize hqcq : qc - c = q
      rw [quantilelower_cashinv (c:=c)]
      have hqcq2 : qc = q + c := by rw[←hqcq]; ring 
      rw [hqcq2] at hqc
      exact hqc 
    · simp 
  · unfold Set.image 
    intro q hq
    obtain ⟨a, ha⟩ := hq 
    rw [quantilelower_cashinv (c:=c)] at ha 
    rw [←ha.2] 
    exact ha.1 

theorem const_monotone_univ : Monotone (fun x ↦ x + c)  := add_left_mono

theorem VaR2_translation_invariant : IsVaR2 P X α v → IsVaR2 P (X+c•1) α (v+c) := by
    intro h 
    unfold IsVaR2 at ⊢ 
    rw [quantilelower_cash_image]
    exact MonotoneOn.map_isGreatest (Monotone.monotoneOn add_left_mono (QuantileLower P X α)) h 

theorem VaR_translation_invariant : VaR[X + c•1 // P, α] = VaR[X + c•1 // P, α] + c := sorry

theorem VaR_positive_homog (hc : c > 0) : FinVaR1 P (fun ω => c * X ω) α = c * FinVaR1 P X α := sorry

end VaR_properties

end Risk

