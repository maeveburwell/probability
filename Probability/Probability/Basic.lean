import Probability.Probability.Induction

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-! 
  # Basic properties for probability spaces and expectations


  The main results:
  - Correspondence between expectations and probabilities (indicator functions)
  - Arithmetic manipulations of random variables
  - The law of total probabilities
  - The law of total expectations
-/

namespace Finprob

variable (P : Finprob) (B : FinRV Bool)

/-- If supported then can be decomposed to the immediate probability and the
remaining probability -/
theorem decompose_supp (supp : P.supported) :
    ℙ[ B // P ] = (B P.ωhead).rec 0 P.phead + (1-P.phead) * ℙ[ B // P.shrink supp ] :=
      by simp [Finprob.phead, Finprob.shrink]
         exact P.ℙ.decompose_supp B P.nonempty_P (P.phead_supp_ne_one supp)

theorem decompose_degen (degen : P.degenerate) : ℙ[ B // P ] = (B P.ωhead).rec 0 P.phead  :=
  by have tz := P.prob.degenerate_tail_zero degen
     simp [Pr.probability, ωhead]
     have almost := P.ℙ.iprod_first_of_tail_zero B P.nonempty_P tz
     rw [List.length_tail] at almost
     exact almost

-- TODO: is there a way to simplify this result to not use induction?
theorem in_prob (P : Finprob) : Prob ℙ[ B // P ] :=
    by have hip := P.phead_prob
       by_cases h : P.supported
       · rw [P.decompose_supp B h]
         have ih := Finprob.in_prob (P.shrink h)
         simp only [Prob] at ⊢ ih hip
         cases B P.ωhead
         · simp only;
           constructor;
           . have prd_zero : 0 ≤ (1 - P.phead) * ℙ[B//P.shrink h] := Rat.mul_nonneg P.phead_prob.of_complement.1 ih.1
             simp_all only [phead, Pr.probability, zero_add]
           · have prd_one : (1 - P.phead) * ℙ[B//P.shrink h] ≤ 1 := mul_le_one₀ P.phead_prob.of_complement.2 ih.1 ih.2
             simp_all only [phead, Pr.probability, zero_add]
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

theorem ge_zero : ℙ[ B // P ] ≥ 0 := (P.in_prob B).left

theorem le_one : ℙ[ B // P ] ≤ 1 := (P.in_prob B).right

end Finprob

------------------------------ List ---------------------------

namespace List

variable (B C : FinRV Bool)

lemma list_compl_sums_to_one (L : List ℚ) : L.iprodb B + L.iprodb (B.not) = L.sum :=
  by induction L with
     | nil => simp [List.iprodb]
     | cons head tail =>
        simp [List.iprodb]
        cases (B tail.length)
        · simp; linarith
        · simp; linarith



lemma law_of_total_probs (L : List ℚ)  : L.iprodb B = L.iprodb (B ∧ᵣ C) + L.iprodb (B ∧ᵣ (¬ᵣC) ) :=
    by induction L with
       | nil => simp [List.iprodb]
       | cons head tail =>
          simp [List.iprodb]
          cases bB: B tail.length
          · cases bC : C tail.length; simp_all; simp_all
          · cases bC : C tail.length
            · simp_all; ring;
            · simp_all; ring;

theorem law_of_total_expectations (L : List ℚ) (X : FinRV ℚ) (B : FinRV Bool) :
  L.iprod X = L.iprod (fun ω => if B ω then X ω else 0) + L.iprod (fun ω => if ¬B ω then X ω else 0) :=
  by induction L with
     | nil => simp [List.iprod]
     | cons head tail =>
        simp [List.iprod]
        cases bB: B tail.length
        · simp_all; ring
        · simp_all; ring
end List


------------------------------ Probablity ---------------------------

namespace Pr

variable (P : Finprob) (B : FinRV Bool) (C : FinRV Bool)


theorem prob_compl_sums_to_one : ℙ[B // P] + ℙ[¬ᵣB // P] = 1 :=
  calc
    ℙ[ B // P ] + ℙ[ ¬ᵣB // P] = P.ℙ.sum := P.ℙ.list_compl_sums_to_one B
    _ = 1 := P.prob.normalized

theorem prob_compl_one_minus : ℙ[¬ᵣB // P] = 1 - ℙ[B // P] :=
    by have := prob_compl_sums_to_one P B
       linarith

theorem law_of_total_probs_bool : ℙ[B // P] = ℙ[ B ∧ᵣ C // P] + ℙ[ B ∧ᵣ ¬ᵣC //P] :=
  P.ℙ.law_of_total_probs B C

theorem conditional_total (h : 0 < ℙ[C // P]) : ℙ[B ∧ᵣ C // P] =  ℙ[ B | C // P] * ℙ[ C // P] :=
  by simp [probability_cnd] at ⊢ h
     have : P.ℙ.iprodb C * (P.ℙ.iprodb C)⁻¹ = 1 :=
            Rat.mul_inv_cancel (P.ℙ.iprodb C) (Ne.symm (ne_of_lt h))
     calc
        P.ℙ.iprodb (B ∧ᵣC) = P.ℙ.iprodb (B ∧ᵣC) * 1 := by ring
        _ = P.ℙ.iprodb (B ∧ᵣC) * (P.ℙ.iprodb C * (P.ℙ.iprodb C)⁻¹) := by rw [←this]
        _ = P.ℙ.iprodb (B ∧ᵣ C) / P.ℙ.iprodb C * P.ℙ.iprodb C := by ring



theorem law_total_prbs_cnd  (h1 : 0 < ℙ[C // P]) (h2 : ℙ[C // P] < 1)
: ℙ[B // P] = ℙ[B | C // P] * ℙ[ C // P] + ℙ[B | ¬ᵣC // P] * ℙ[¬ᵣC // P] :=
        by have h2' : 0 < ℙ[¬ᵣC // P] := by rw [prob_compl_one_minus]; linarith
           rw [←conditional_total P B C h1]
           rw [←conditional_total P B (¬ᵣC) h2']
           exact law_of_total_probs_bool P B C


variable {K : ℕ}  {L : FinRV (Fin K)}

theorem law_of_total_probs : ∑ i : Fin K, ℙ[ B ∧ᵣ (L =ᵣ i) // P ] = ℙ[B // P] := sorry

end Pr

------------------------------ Expectation ---------------------------

namespace PMF

variable {K : ℕ}  {L : FinRV (Fin K)}
variable {pmf : Fin K → ℚ}
variable {P : Finprob}

theorem pmf_rv_k_ge_1 (h : PMF pmf P L)  : 0 < K :=
  match K with
  | Nat.zero => Fin.elim0 (L 0)
  | Nat.succ n => Nat.succ_pos n

end PMF

------------------------------ Expectation ---------------------------

namespace Ex

variable {P : Finprob}
variable {K : ℕ} {X : FinRV ℚ} {B : FinRV Bool} {L : FinRV (Fin K)}

variable {pmf : Fin K → ℚ}

theorem law_total_exp_bool  (h1 : 0 < ℙ[B // P]) (h2 : 0 < ℙ[¬ᵣB // P]) :
    𝔼[X // P] = 𝔼[X | B // P] * ℙ[B // P] + 𝔼[X | ¬ᵣB // P] * ℙ[¬ᵣB // P] :=
  by
    simp [expect, expect_cnd] at ⊢ h1 h2
    have h1' : P.ℙ.iprodb B ≠ 0 := Ne.symm (ne_of_lt h1)
    have h2' : P.ℙ.iprodb (¬ᵣB) ≠ 0 := Ne.symm (ne_of_lt h2)
    have h3' : P.ℙ.iprod X = P.ℙ.iprod (fun ω => if B ω then X ω else 0) + P.ℙ.iprod (fun ω => if ¬B ω then X ω else 0) :=
      P.ℙ.law_of_total_expectations X B
    rw [h3']
    simp_all
    sorry

-- TODO: The following derivations should be our focus

---- STEP 1:

-- LOTUS: the law of the unconscious statistician (or similar)
theorem LOTUS {g : Fin K → ℚ} (h : PMF pmf P L): 
    𝔼[ g ∘ L // P ] = ∑ i : Fin K, (pmf i) * (g i) := sorry

-- this proof will rely on the extensional property of function (functions are the same if they
-- return the same value for the same inputs; for all inputs)
theorem condexp_pmf : 𝔼[ X |ᵣ L  // P] =  (fun i ↦ 𝔼[ X | (L =ᵣ i) // P]) ∘ L := 
  by sorry


theorem expexp : 𝔼[ 𝔼[ X |ᵣ L // P] // P ] = ∑ i : Fin K, 𝔼[ X | L =ᵣ i // P] * ℙ[ L =ᵣ i // P] := sorry

-- STEP 2: 

theorem ind_eq_zero_of_cond_empty (h : ℙ[B // P] = 0) : 
        ∀ ω : (Fin P.length), (𝕀ᵣ B) ω = 0 := 
        by sorry


theorem μ_eq_zero_of_cond_empty (h : ℙ[B // P] = 0) : μ ℙ X (𝕀ᵣ B) = 0 := sorry

theorem exp_prod_μ (i : Fin K) : 𝔼[ X | B // P] * ℙ[ B // P] 
                                  = μ P X (𝕀ᵣ B) := 
    by unfold expect_cnd
       by_cases h: ℙ[B//P] = 0
       · rw [μ_eq_zero_of_cond_empty h]
         ring 
       · simp_all only [isUnit_iff_ne_zero, ne_eq, not_false_eq_true, 
                         IsUnit.div_mul_cancel]

-- STEP 3:
-- proves that μ distributes over the random variables
theorem μ_dist (h : Fin K → FinRV ℚ) : ∑ i : Fin K, μ P X (h i) = μ P X (fun ω ↦ ∑ i : Fin K, (h i) ω) := sorry
 
theorem fin_sum : ∀ ω : ℕ, ∑ i : Fin K, (𝕀ᵣ (L =ᵣ i)) ω = 1 := sorry

theorem exp_eq_exp_cond_true : 𝔼[X // P] = μ P X (fun ω ↦ 1 ) := sorry 


-- TODO: need to sum all probabilities


example {f g : ℕ → ℚ} {m : ℕ} (h : ∀ n : ℕ, f n = g n) : ∑ i : Fin m, f i = ∑ i : Fin m, g i := 
    by apply Finset.sum_congr
       · simp
       · simp_all  
  
-- STEP 4: We now use the results above to prove the law of total expectations
theorem law_total_exp : 𝔼[ 𝔼[ X |ᵣ L // P] // P ] = 𝔼[ X // P] := 
  calc
    𝔼[𝔼[X |ᵣ L // P] // P ] = ∑ i : Fin K, 𝔼[ X | L =ᵣ i // P ] * ℙ[ L =ᵣ i // P] := expexp
    _ =  ∑ i : Fin K, μ P X (𝕀ᵣ (L =ᵣ i)) := by apply Fintype.sum_congr; 
                                                exact fun a => exp_prod_μ (L K)
    _ =  μ P X (fun ω ↦  ∑ i : Fin K, (𝕀ᵣ (L =ᵣ i)) ω) :=  μ_dist fun i => 𝕀ᵣ (L=ᵣi)
    _ =  μ P X (fun ω ↦  1) :=  by conv => lhs; congr; rfl; rfl; intro ω; exact fin_sum ω
    _ = 𝔼[X // P]  := exp_eq_exp_cond_true.symm

end Ex
