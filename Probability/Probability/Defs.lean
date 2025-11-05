import Probability.Probability.Prelude

--------------------------- Findist ---------------------------------------------------------------<F2>

/-- Finite probability distribution on a set-like list (non-duplicates)  -/
structure Findist (N : ℕ)  : Type where
  ℙ : List ℚ                      -- probabilities
  simplex : LSimplex ℙ            -- proof of a measure
  lmatch : ℙ.length = N           -- correct length of probability


namespace Findist

abbrev Delta : ℕ → Type := Findist
abbrev Δ : ℕ → Type := Delta

variable {N : ℕ} (F : Findist N)

abbrev degenerate : Bool := F.simplex.degenerate
abbrev supported : Bool := F.simplex.supported

theorem supp_not_degen (supp : F.supported) : ¬ F.degenerate :=
        by simp_all [supported, degenerate]

@[simp]
theorem nonempty (F : Findist N) : N ≥ 1 :=
  F.lmatch ▸ List.length_pos_iff.mpr F.simplex.npt

@[simp]
theorem nonempty_P : F.ℙ ≠ [] :=
  by have := F.simplex.npt
     intro a; contradiction

def singleton : Findist 1 :=
    {ℙ := [1]
     simplex := LSimplex.singleton,
     lmatch := by simp_all only [List.length_cons, List.length_nil, zero_add]}

abbrev phead := F.simplex.phead

@[simp]
theorem phead_inpr : F.phead ∈ F.ℙ := List.head_mem F.nonempty_P

@[simp]
theorem phead_prob : Prob F.phead := F.simplex.mem_prob F.phead F.phead_inpr

theorem nondegenerate_head (supp : F.supported) : F.phead < 1 :=
  by have h1 := Findist.phead_prob F
     simp_all only [supported, LSimplex.supported, LSimplex.degenerate,
                    LSimplex.phead, beq_iff_eq, phead, gt_iff_lt]
     simp! only [decide_not, Bool.not_eq_eq_eq_not, not, decide_eq_false_iff_not] at supp
     simp [Prob] at h1
     exact lt_of_le_of_ne h1.2 supp

end Findist


/-- Finite probability space. See Finsample for the definition of the sample space. -/
structure Finprob : Type where
  ℙ : List ℚ
  prob : LSimplex ℙ

lemma List.unique_head_notin_tail (L : List τ) (ne : L ≠ []) (nodup : L.Nodup) :
      L.head ne ∉ L.tail :=
  by induction L
     · simp at ne
     · simp [List.head, List.tail]
       simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, List.nodup_cons]

namespace Finprob

variable (P : Finprob)

@[simp]
def length := P.ℙ.length

def singleton : Finprob :=
   ⟨ [1], LSimplex.singleton ⟩

def grow {p : ℚ} (prob : Prob p) : Finprob :=
  ⟨P.ℙ.grow p, P.prob.grow prob⟩

/-- all probability in the head -/
abbrev degenerate  : Bool := P.prob.degenerate
abbrev supported  : Bool := P.prob.supported

theorem not_degen_supp (supp : ¬P.degenerate) : P.supported :=
  by simp_all [Finprob.degenerate, Finprob.supported]

theorem degen_of_not_supp (notsupp : ¬P.supported) : P.degenerate :=
  by simp_all [Finprob.degenerate, Finprob.supported]


theorem nonempty : ¬P.ℙ.isEmpty :=
  by intro a;
     simp_all only [LSimplex.nonempty P.prob, List.isEmpty_iff]

--TODO: try to shorten/simplify the theorem below
theorem length_gt_zero : P.length ≥ 1 :=
  by
    simp [Finprob.length]
    have hne : P.ℙ ≠ [] := by
      intro hnil
      have : P.ℙ.isEmpty = true := by simp [List.isEmpty, hnil]
      exact P.nonempty this
    exact Nat.succ_le_of_lt (List.length_pos_iff.mpr hne)


theorem nonempty_P : P.ℙ ≠ [] := P.prob.nonempty

@[simp]
def phead := P.ℙ.head P.nonempty_P

@[simp]
def ωhead := P.length - 1

theorem phead_inpr : P.phead ∈ P.ℙ := List.head_mem P.nonempty_P

theorem phead_prob : Prob P.phead :=
  P.prob.mem_prob P.phead P.phead_inpr

theorem phead_supp_ne_one (supp : P.supported) : P.phead ≠ 1 :=
        by simp [Finprob.supported, LSimplex.supported, LSimplex.degenerate, LSimplex.phead] at supp
           simp [Finprob.phead]
           exact supp

theorem len_ge_one : P.length ≥ 1 :=
  by simp [Finprob.length]
     have h := P.prob.nonempty
     have : P.ℙ.length ≠ 0 := by simp_all only [ne_eq, List.length_eq_zero_iff, not_false_eq_true]
     exact Nat.one_le_iff_ne_zero.mpr this

end Finprob


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

/-- Boolean indicator function -/
def indicator (cond : Bool) : ℚ := cond.rec 0 1

abbrev 𝕀 : Bool → ℚ := indicator

/-- Indicator is 0 or 1 -/
theorem ind_zero_one (cond : τ → Bool) : ( (𝕀∘cond) ω = 1) ∨ ((𝕀∘cond) ω = 0) := by
    by_cases h : cond ω
    · left; simp only [Function.comp_apply, h, indicator]
    · right; simp only [Function.comp_apply, h, indicator]


end RandomVariable


------------------------------ Section Probability ---------------------------

section Probability

----- standard probability


variable (P : Finprob) (B : FinRV Bool) (C : FinRV Bool)

/-- Probability of B -/
def probability : ℚ :=  P.ℙ.iprodb B

notation "ℙ[" B "//" P "]" => probability P B

/-- Conditional probability of B -/
def probability_cnd : ℚ := ℙ[ B ∧ᵣ C // P ] / ℙ[ C // P ]

--- main decomposition properties

theorem Prob.true_one : ℙ[ fun _ ↦ true // P] = 1 :=
    by simp only [probability]; rw [List.iprodb_true_sum]; exact P.prob.normalized

--- sums

theorem List.list_compl_sums_to_one (L : List ℚ) : L.iprodb B + L.iprodb (B.not) = L.sum :=
  by induction L with
     | nil => simp [List.iprodb]
     | cons head tail =>
        simp [List.iprodb]
        cases (B tail.length)
        · simp; linarith
        · simp; linarith


theorem List.law_of_total_probs (L : List ℚ)  : L.iprodb B = L.iprodb (B ∧ᵣ C) + L.iprodb (B ∧ᵣ (¬ᵣC) ) :=
    by induction L with
       | nil => simp [List.iprodb]
       | cons head tail =>
          simp [List.iprodb]
          cases bB: B tail.length
          · cases bC : C tail.length; simp_all; simp_all
          · cases bC : C tail.length
            · simp_all; ring;
            · simp_all; ring;

theorem Prob.prob_compl_sums_to_one : ℙ[B // P] + ℙ[¬ᵣB // P] = 1 :=
  calc
    ℙ[ B // P ] + ℙ[ ¬ᵣB // P] = P.ℙ.sum := P.ℙ.list_compl_sums_to_one B
    _ = 1 := P.prob.normalized

theorem Prob.prob_compl_one_minus : ℙ[¬ᵣB // P] = 1 - ℙ[B // P] :=
    by have := Prob.prob_compl_sums_to_one P B
       linarith


theorem Prob.law_of_total_probs : ℙ[B // P] = ℙ[ B ∧ᵣ C // P] + ℙ[ B ∧ᵣ ¬ᵣC //P] := P.ℙ.law_of_total_probs B C

---- conditional probability

notation "ℙ[" B "|" C "//" P "]" => probability_cnd P B C

theorem Prob.conditional_total (h : 0 < ℙ[C // P]) : ℙ[B ∧ᵣ C // P] =  ℙ[ B | C // P] * ℙ[ C // P] :=
  by simp [probability_cnd] at ⊢ h
     have : P.ℙ.iprodb C * (P.ℙ.iprodb C)⁻¹ = 1 := Rat.mul_inv_cancel (P.ℙ.iprodb C) (Ne.symm (ne_of_lt h))
     calc
        P.ℙ.iprodb (B ∧ᵣC) = P.ℙ.iprodb (B ∧ᵣC) * 1 := by ring
        _ = P.ℙ.iprodb (B ∧ᵣC) * (P.ℙ.iprodb C * (P.ℙ.iprodb C)⁻¹) := by rw [←this]
        _ = P.ℙ.iprodb (B ∧ᵣ C) / P.ℙ.iprodb C * P.ℙ.iprodb C := by ring


theorem Prob.law_of_total_probs_cnd
  (h1 : 0 < ℙ[C // P]) (h2 : ℙ[C // P] < 1)  : ℙ[B // P] = ℙ[B | C // P] * ℙ[ C // P] + ℙ[B | ¬ᵣC // P] * ℙ[¬ᵣC // P] :=
        by have h2' : 0 < ℙ[¬ᵣC // P] := by rw [prob_compl_one_minus]; linarith
           rw [←Prob.conditional_total P B C h1]
           rw [←Prob.conditional_total P B (¬ᵣC) h2']
           exact law_of_total_probs P B C

end Probability

section Expectations

def List.iprod (ℙ : List ℚ) (X : FinRV ℚ) : ℚ :=
    match ℙ with
    | [] => 0
    | head :: tail =>  head * (X tail.length) + tail.iprod X


variable (P : Finprob) (X Y Z: FinRV ℚ) (B : FinRV Bool)

def expect : ℚ := P.ℙ.iprod X

notation "𝔼[" X "//" P "]" => expect P X

-- expectation for a joint probability space and random variable
notation "𝔼[" PX "]" => expect PX.1 PX.2



-- conditional expectation

def expect_cnd : ℚ := P.ℙ.iprod X / P.ℙ.iprodb B

notation "𝔼[" X "|" B "//" P "]" => expect_cnd P X B

-- expectation for a joint probability space and random variable
notation "𝔼[" PX "]" => expect PX.1 PX.2
notation "𝔼[" PX "|" B "]" => expect_cnd PX.1 PX.2 B

-- conditional expectation: conditioning on a random variable: this defintion creates a probability
-- space and a random variable

variable {K : ℕ} (D : FinRV (Fin K.succ))  -- a discrete random variable with K+1 values

theorem List.law_of_total_expectations (L : List ℚ) (X : FinRV ℚ) (B : FinRV Bool) :
  L.iprod X = L.iprod (fun ω => if B ω then X ω else 0) + L.iprod (fun ω => if ¬B ω then X ω else 0) :=
  by induction L with
     | nil => simp [List.iprod]
     | cons head tail =>
        simp [List.iprod]
        cases bB: B tail.length
        · simp_all; ring
        · simp_all; ring

theorem Prob.law_of_total_expectation (P : Finprob) (X : FinRV ℚ) (B : FinRV Bool)
  (h1 : 0 < ℙ[B // P]) (h2 : 0 < ℙ[¬ᵣB // P]) :
  𝔼[X // P] = 𝔼[X | B // P] * ℙ[B // P] + 𝔼[X | ¬ᵣB // P] * ℙ[¬ᵣB // P] :=
  by
    simp [expect, expect_cnd] at ⊢ h1 h2
    have h1' : P.ℙ.iprodb B ≠ 0 := Ne.symm (ne_of_lt h1)
    have h2' : P.ℙ.iprodb (¬ᵣB) ≠ 0 := Ne.symm (ne_of_lt h2)

    have h3' : P.ℙ.iprod X = P.ℙ.iprod (fun ω => if B ω then X ω else 0) + P.ℙ.iprod (fun ω => if ¬B ω then X ω else 0) :=
      List.law_of_total_expectations P.ℙ X B
    rw [h3']
    simp_all
    sorry

end Expectations

