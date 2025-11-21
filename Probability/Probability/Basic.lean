--import Probability.Probability.Induction

import Probability.Probability.Defs

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

namespace Findist

variable {n : ℕ} (P : Findist n) (B : FinRV n Bool)

-- TODO: is there a way to simplify this result to not use induction?
theorem in_prob (P : Findist n) : Prob ℙ[B // P] := sorry

theorem ge_zero : ℙ[ B // P ] ≥ 0 := (P.in_prob B).left

theorem le_one : ℙ[B // P] ≤ 1 := (P.in_prob B).right

end Findist

------------------------------ Probablity ---------------------------

namespace Pr

variable (P : Findist n) (B : FinRV n Bool) (C : FinRV n Bool)

theorem prob_compl_sums_to_one : ℙ[B // P] + ℙ[¬ᵣB // P] = 1 := sorry

theorem prob_compl_one_minus : ℙ[¬ᵣB // P] = 1 - ℙ[B // P] :=
    by have := prob_compl_sums_to_one P B
       linarith

@[simp]
lemma refold_probability (P : Findist n) (B : FinRV n Bool) :
    P.p ⬝ᵥ (𝕀 ∘ B) = ℙ[B // P] := rfl

theorem law_of_total_probs_bool : ℙ[B // P] = ℙ[ B * C // P] + ℙ[ B * (¬ᵣC) //P] :=
  by
    unfold Pr.probability
    have h : ∀ i : Fin n, (𝕀 (B i)) = (𝕀 (B i * C i)) + (𝕀 (B i * (¬ᵣ C) i)) :=
      by
        intro i
        by_cases hB : B i
        · by_cases hC : C i
          · simp [hB, hC, FinRV.not, indicator]
          · simp [hB, hC, FinRV.not, indicator]
        · by_cases hC : C i
          · simp [hB, hC, FinRV.not, indicator]
          · simp [hB, hC, FinRV.not, indicator]
    sorry ---I tried to do this proof but got stuck, feel free to delete my work


theorem conditional_total (h : 0 < ℙ[C // P]) : ℙ[B * C // P] =  ℙ[ B | C // P] * ℙ[ C // P] :=
  sorry
  -- by simp [probability_cnd] at ⊢ h
  --    have : P.ℙ.iprodb C * (P.ℙ.iprodb C)⁻¹ = 1 :=
  --           Rat.mul_inv_cancel (P.ℙ.iprodb C) (Ne.symm (ne_of_lt h))
  --    calc
  --       P.ℙ.iprodb (B ∧ᵣC) = P.ℙ.iprodb (B ∧ᵣC) * 1 := by ring
  --       _ = P.ℙ.iprodb (B ∧ᵣC) * (P.ℙ.iprodb C * (P.ℙ.iprodb C)⁻¹) := by rw [←this]
  --       _ = P.ℙ.iprodb (B ∧ᵣ C) / P.ℙ.iprodb C * P.ℙ.iprodb C := by ring


theorem law_total_prbs_cnd  (h1 : 0 < ℙ[C // P]) (h2 : ℙ[C // P] < 1)
: ℙ[B // P] = ℙ[B | C // P] * ℙ[ C // P] + ℙ[B | ¬ᵣC // P] * ℙ[¬ᵣC // P] :=
        by have h2' : 0 < ℙ[¬ᵣC // P] := by rw [prob_compl_one_minus]; linarith
           rw [←conditional_total P B C h1]
           rw [←conditional_total P B (¬ᵣC) h2']
           exact law_of_total_probs_bool P B C

variable {K : ℕ}  {L : FinRV n (Fin K)}

theorem law_of_total_probs : ∑ i : Fin K, ℙ[ B * (L =ᵣ i) // P ] = ℙ[B // P] := sorry

end Pr

------------------------------ Expectation ---------------------------

namespace PMF

variable {K : ℕ}  {L : FinRV n (Fin K)}
variable {pmf : Fin K → ℚ}
variable {P : Findist n}

-- em: is the theorem below true? ma: Hmm, I think it is no longer true; I wonder why it was true in the 
-- first place before
theorem pmf_rv_k_ge_1 (h : PMF pmf P L)  : 0 < K :=
  by cases' K with  z nz  
     · unfold PMF at h 
       sorry 
     · exact Nat.zero_lt_succ z

end PMF

------------------------------ Expectation ---------------------------

namespace Ex

variable {P : Findist n}
variable {K : ℕ} {X : FinRV n ℚ} {B : FinRV n Bool} {L : FinRV n (Fin K)}

variable {pmf : Fin K → ℚ}

example (f g : Fin K → ℚ) (h : f = g) : ∑ i : Fin K, f i = ∑ i : Fin K, g i := by
  let ff := f
  have h2 : ff = f := by unfold ff; rfl
  rw [←h2]
  rw [←h]


theorem prob_eq_exp_ind : ℙ[B // P] = 𝔼[𝕀 ∘ B // P] := sorry

-- TODO: The following derivations should be our focus

---- STEP 1:
variable  (g : Fin K → ℚ)

abbrev 𝕀ᵣ (B : FinRV n Bool) : FinRV n ℚ := fun ω => 𝕀 (B ω)

theorem fin_sum_g: ∀ ω : Fin n, ∑ i : Fin K, (g i) * (𝕀ᵣ (L =ᵣ i)) ω = g (L ω) := by
  intro ω
  unfold 𝕀ᵣ FinRV.eq 𝕀 indicator
  generalize hk : L ω = k
  let f i := g i * (decide (k = i)).rec 0 1
  have h1 (i : Fin K) : k ≠ i → f i = 0 := by intro h; simp_all [f]
  have h2 (i : Fin K ) : k = i → f i = g k := by intro h; simp_all [f]
  have hh : f = (fun i ↦ g i * (decide (k = i)).rec 0 1) :=  by simp [f]
  rw [←hh]
  rw [←h2 k rfl]
  apply Finset.sum_eq_single_of_mem
  · simp only [Finset.mem_univ]
  · intro b _ hneq
    exact h1 b hneq.symm

theorem idktheorem (P : Findist n) (L : FinRV n (Fin K)) (g : Fin K → ℚ) :
    𝔼[g ∘ L // P] = ∑ i : Fin K, g i * ℙ[L =ᵣ i // P] := sorry

-- LOTUS: the law of the unconscious statistician (or similar)
theorem LOTUS {g : Fin K → ℚ} (h : PMF pmf P L):
        𝔼[ g ∘ L // P ] = ∑ i : Fin K, (pmf i) * (g i) :=
  by
     rw [idktheorem P L g]
     apply Fintype.sum_congr
     intro i
     rw [h i]
     ring

-- this proof will rely on the extensional property of function (functions are the same if they
-- return the same value for the same inputs; for all inputs)
theorem condexp_pmf : 𝔼[ X |ᵣ L  // P] =  (fun i ↦ 𝔼[ X | (L =ᵣ i) // P]) ∘ L :=
  by sorry


theorem expexp : 𝔼[ 𝔼[ X |ᵣ L // P] // P ] = ∑ i : Fin K, 𝔼[ X | L =ᵣ i // P] * ℙ[ L =ᵣ i // P] := sorry

-- STEP 2:

--is this theorem true??
--theorem ind_eq_zero_of_cond_empty (h : ℙ[B // P] = 0) : ∀ ω : (Fin P.length), (𝕀ᵣ B) ω = 0 := sorry


theorem μ_eq_zero_of_cond_empty (h : ℙ[B // P] = 0) : 𝔼[X * (𝕀ᵣ B) // P] = 0 := sorry

theorem exp_prod_μ  : 𝔼[X | B // P] * ℙ[B // P] = 𝔼[X * (𝕀ᵣ B) // P] :=
  sorry
    -- by unfold expect_cnd
    --    by_cases h: ℙ[B//P] = 0
    --    · rw [μ_eq_zero_of_cond_empty h]
    --      ring_nf
    --    · simp_all only [isUnit_iff_ne_zero, ne_eq, not_false_eq_true,
    --                      IsUnit.div_mul_cancel]

-- STEP 3:
-- proves that μ distributes over the random variables


theorem μ_dist (h : Fin K → FinRV n ℚ) :
    ∑ i : Fin K, 𝔼[ X * (h i) // P] = 𝔼[ X * (fun ω ↦ ∑ i : Fin K, (h i) ω) // P] := sorry

theorem fin_sum : ∀ ω : Fin n, ∑ i : Fin K, (𝕀ᵣ (L =ᵣ i)) ω = 1 :=
    by have := fin_sum_g 1 (L := L)
       simp_all

theorem exp_eq_exp_cond_true : 𝔼[X // P] = 𝔼[X * (fun ω ↦ 1 ) // P] := sorry


-- TODO: need to sum all probabilities


example {f g : ℕ → ℚ} {m : ℕ} (h : ∀ n : ℕ, f n = g n) :
    ∑ i : Fin m, f i = ∑ i : Fin m, g i :=
    by apply Finset.sum_congr
       · simp
       · simp_all

-- STEP 4: We now use the results above to prove the law of total expectations
theorem law_total_exp : 𝔼[ 𝔼[ X |ᵣ L // P] // P ] = 𝔼[ X // P] :=
  calc
    𝔼[𝔼[X |ᵣ L // P] // P ] = ∑ i : Fin K, 𝔼[ X | L =ᵣ i // P ] * ℙ[ L =ᵣ i // P] := expexp
    _ =  ∑ i : Fin K, 𝔼[X * (𝕀ᵣ (L =ᵣ i)) // P] := by
          apply Finset.sum_congr
          · rfl 
          · exact fun a _ ↦ exp_prod_μ 
    _ = 𝔼[X * (fun ω ↦  ∑ i : Fin K, (𝕀ᵣ (L =ᵣ i)) ω) // P] :=  μ_dist fun i => 𝕀ᵣ (L=ᵣi)
    _ = 𝔼[X * (fun ω ↦  1) // P] := by
          unfold expect; conv => lhs; congr; rfl; congr; rfl; intro ω; exact fin_sum ω
    _ = 𝔼[X // P]  := exp_eq_exp_cond_true.symm

end Ex
