/-
The file defines probability and expectation operators along with their basic properties
-/

import Probability.Probability.Basic


------------------------------ Section Probability ---------------------------

section Probability

----- standard probability

/-- Probability of a random variable. Does not enforce normalization -/
def List.iprodb (ℙ : List ℚ) (B : FinRV Bool) : ℚ :=
    match ℙ with
    | [] => 0
    | head :: tail =>  (B tail.length).rec 0 head + tail.iprodb B


variable (P : Finprob) (B : FinRV Bool) (C : FinRV Bool)

variable (L : List ℚ)

theorem List.scale_innerprod  (x : ℚ) : (L.scale x).iprodb B = x * (L.iprodb B) :=
  by induction L with
     | nil => simp_all [List.scale, List.iprodb]
     | cons head tail =>
            simp_all [List.iprodb, List.scale]
            cases B tail.length
            · simp_all
            · simp_all
              ring

theorem List.decompose_supp (h : L ≠ []) (ne1 : L.head h ≠ 1):
    L.iprodb B = (B (L.length - 1)).rec 0 (L.head h) + (1-L.head h) * (L.shrink.iprodb B)  :=
    by conv => lhs; unfold iprodb
       cases L with
       | nil => simp at h
       | cons head tail =>
        simp [List.shrink]
        have := tail.scale_innerprod B (1-head)⁻¹
        simp_all
        have hnz : 1 - head ≠ 0 :=
          by by_contra; have : head = 1 := by linarith;
             contradiction
        calc
          tail.iprodb B = 1 * tail.iprodb B := by ring
          _ = (1 - head) * (1 - head)⁻¹ * tail.iprodb B  :=
              by rw [Rat.mul_inv_cancel (1-head) hnz]
          _ = (1 - head) * ((1 - head)⁻¹ * tail.iprodb B ) := by ring

theorem List.iprod_eq_zero_of_zeros (hz : ∀ p ∈ L, p = 0) : L.iprodb B = 0 :=
  by induction L with
     | nil => simp [iprodb]
     | cons head tail => simp_all [iprodb]; cases B tail.length; simp; simp


theorem List.iprod_first_of_tail_zero  (hn : L ≠ []) (hz : ∀ p ∈ L.tail, p = 0) :
   L.iprodb B = (B L.tail.length).rec 0 (L.head hn)  :=
   by unfold iprodb
      cases L
      · contradiction
      · simp; simp at hz; (expose_names; exact iprod_eq_zero_of_zeros B tail hz)

lemma List.iprodb_true_sum : L.iprodb (fun _ ↦ true) = L.sum :=
    by induction L
       · simp only  [iprodb, sum_nil]
       · simp_all only [iprodb, sum_cons]


/-- Probability of B -/
def probability : ℚ :=  P.ℙ.iprodb B

notation "ℙ[" B "//" P "]" => probability P B

/-- Conditional probability of B -/
def probability_cnd : ℚ := ℙ[ B ∧ᵣ C // P ] / ℙ[ C // P ]

--- main decomposition properties

/-- If supported then can be decomposed to the immediate probability and the
remaining probability -/
theorem Finprob.decompose_supp (supp : P.supported) :
    ℙ[ B // P ] = (B P.ωhead).rec 0 P.phead + (1-P.phead) * ℙ[ B // P.shrink supp ] :=
      by simp [Finprob.phead, Finprob.shrink]
         exact P.ℙ.decompose_supp B P.nonempty_P (P.phead_supp_ne_one supp)

theorem Finprob.decompose_degen (degen : P.degenerate) : ℙ[ B // P ] = (B P.ωhead).rec 0 P.phead  :=
  by have tz := P.prob.degenerate_tail_zero degen
     simp [probability, Finprob.ωhead]
     have almost := P.ℙ.iprod_first_of_tail_zero B P.nonempty_P tz
     rw [List.length_tail] at almost
     exact almost

--- basic properties

theorem Finprob.in_prob (P : Finprob) : Prob ℙ[ B // P ] :=
    by have hip := P.phead_prob
       by_cases h : P.supported
       · rw [P.decompose_supp B h]
         have ih := Finprob.in_prob (P.shrink h)
         simp only [Prob] at ⊢ ih hip
         cases B P.ωhead
         · simp only;
           constructor;
           . have prd_zero : 0 ≤ (1 - P.phead) * ℙ[B//P.shrink h] := Rat.mul_nonneg P.phead_prob.of_complement.1 ih.1
             simp_all only [phead, probability, zero_add]
           · have prd_one : (1 - P.phead) * ℙ[B//P.shrink h] ≤ 1 := mul_le_one₀ P.phead_prob.of_complement.2 ih.1 ih.2
             simp_all only [phead, probability, zero_add]
         · simp only;
           constructor;
           · calc
               0 ≤ ℙ[B//P.shrink h] := ih.1
               _ ≤ P.phead * 1 + (1 - P.phead) * ℙ[B//P.shrink h] := P.phead_prob.lower_bound_snd ih.2
               _ = P.phead  + (1 - P.phead) * ℙ[B//P.shrink h] := by ring
           · calc
               P.phead + (1 - P.phead) * ℙ[B//P.shrink h] =
                P.phead * 1 + (1 - P.phead) * ℙ[B//P.shrink h] := by ring
               _ ≤ 1 := P.phead_prob.upper_bound_fst ih.2
       · rw [P.decompose_degen B (P.degen_of_not_supp h) ]
         cases B P.ωhead
         · simp_all
         · simp_all
    termination_by P.length
    decreasing_by exact shrink_length_lt P h

theorem Prob.ge_zero : ℙ[ B // P ] ≥ 0 := (P.in_prob B).left

theorem Prob.le_one : ℙ[ B // P ] ≤ 1 := (P.in_prob B).right

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
  (h1 : 0 < ℙ[C // P]) (h2 : ℙ[C // P] < 1)  : ℙ[B // P] = ℙ[B | C // P] * ℙ[ C // P] + ℙ[B | ¬ᵣC //P] * ℙ[¬ᵣC // P] :=
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



