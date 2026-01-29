import Probability.Probability.Defs

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

import Mathlib.Data.Fin.Tuple.Sort -- for Equiv.Perm and permutation operations


/-!
  # Basic properties for probability spaces and expectations

  The main results:
  - LOTUS: The law of the unconscious statistician 
  - The law of total expectations
  - The law of total probabilities
-/

namespace Findist

variable {n : ℕ} {P : Findist n} {B : FinRV n Bool}

theorem ge_zero : 0 ≤ ℙ[B // P] := 
    by rw [prob_eq_exp_ind]
       calc 0 = 𝔼[0 //P] := exp_const.symm 
            _ ≤ 𝔼[𝕀 ∘ B//P] := exp_monotone ind_nneg
       

theorem le_one : ℙ[B // P] ≤ 1 := 
    by rw [prob_eq_exp_ind]
       calc 𝔼[𝕀 ∘ B//P] ≤ 𝔼[1 // P] := exp_monotone ind_le_one 
            _ = 1 := exp_const 

theorem in_prob (P : Findist n) : Prob ℙ[B // P] := ⟨ge_zero, le_one⟩

end Findist


-------- Mnotonicity of random variables --------------------------------------------

section RandomVariables

variable {n : ℕ} {P : Findist n} {A B : FinRV n Bool} {X Y : FinRV n ℚ} {t t₁ t₂ : ℚ}

theorem rvle_monotone (h1 : X ≤ Y) (h2: t₁ ≤ t₂) : 𝕀 ∘ (Y ≤ᵣ t₁) ≤ 𝕀 ∘ (X ≤ᵣ t₂) := by 
    intro ω   
    by_cases h3 : Y ω ≤ t₁
    · have h4 : X ω ≤ t₂ := le_trans (le_trans (h1 ω) h3) h2
      simp [FinRV.leq, 𝕀, indicator, h3, h4] 
    · by_cases h5 : X ω ≤ t₂
      repeat simp [h3, h5, 𝕀, indicator] 

theorem rvlt_monotone (h1 : X ≤ Y) (h2: t₁ ≤ t₂) : 𝕀 ∘ (Y <ᵣ t₁) ≤ 𝕀 ∘ (X <ᵣ t₂) := by 
    intro ω   
    by_cases h3 : Y ω < t₁
    · have h4 : X ω < t₂ := 
        calc X ω ≤ Y ω := h1 ω
             _ < t₁ := h3
             _ ≤ t₂ := h2 
      simp [FinRV.lt, 𝕀, indicator, h3, h4] 
    · by_cases h5 : X ω < t₂
      repeat simp [h3, h5, 𝕀, indicator] 

      
end RandomVariables

------------------------------ Probability ---------------------------

variable {n : ℕ} {P : Findist n} {A B C : FinRV n Bool} {X Y : FinRV n ℚ} {t t₁ t₂ : ℚ}

theorem prob_compl_sums_to_one : ℙ[B // P] + ℙ[¬ᵣB // P] = 1 := 
    by rw [prob_eq_exp_ind, prob_eq_exp_ind, ←exp_additive_two, one_of_ind_bool_or_not]
       exact exp_one 

theorem prob_compl_one_minus : ℙ[¬ᵣB // P] = 1 - ℙ[B // P] :=
    by rw [←prob_compl_sums_to_one (P:=P) (B:=B)]; ring 

theorem rv_le_compl_gt : (X ≤ᵣ t) + (X >ᵣ t) = 1 := by
  ext ω
  unfold FinRV.leq FinRV.gt
  simp
  exact le_or_gt (X ω) t

theorem prob_le_compl_gt : ℙ[X ≤ᵣ t // P] + ℙ[X >ᵣ t // P] = 1 := by
  rw [prob_eq_exp_ind, prob_eq_exp_ind, ← exp_additive_two]
  have h : (𝕀 ∘ (X ≤ᵣ t)) + (𝕀 ∘ (X >ᵣ t)) = (1 : FinRV n ℚ) := by
    ext ω
    unfold FinRV.leq FinRV.gt
    simp [𝕀, indicator]
    by_cases h1 : X ω ≤ t
    · have h2 : ¬ (X ω > t) := not_lt_of_ge h1
      simp [h1, h2]
    · have h3 : X ω > t := lt_of_not_ge h1
      simp [h1, h3]
  rw [h]
  exact exp_one

theorem prob_gt_of_le : ℙ[X >ᵣ t // P] = 1 -  ℙ[X ≤ᵣ t // P] := by
  rw [← prob_le_compl_gt]
  ring

theorem prob_le_of_gt :  ℙ[X ≤ᵣ t // P] = 1 - ℙ[X >ᵣ t // P] := by
  rw [← prob_le_compl_gt]
  ring

theorem prob_lt_compl_ge : ℙ[X <ᵣ t // P] + ℙ[X ≥ᵣ t // P] = 1 := by
  rw [prob_eq_exp_ind, prob_eq_exp_ind, ← exp_additive_two]
  have h : (𝕀 ∘ (X <ᵣ t)) + (𝕀 ∘ (X ≥ᵣ t)) = (1 : FinRV n ℚ) := by
    ext ω
    unfold FinRV.lt FinRV.geq
    simp [𝕀, indicator]
    by_cases h1 : X ω < t
    · have h2 : ¬ (X ω ≥ t) := not_le_of_gt h1
      simp [h1, h2]
    · have h3 : X ω ≥ t := le_of_not_gt h1
      simp [h1, h3]
  rw [h]
  exact exp_one

theorem prob_ge_of_lt : ℙ[X ≥ᵣ t // P] = 1 -  ℙ[X <ᵣ t // P] := by
  rw [← prob_lt_compl_ge]
  ring

theorem prob_lt_of_ge :  ℙ[X <ᵣ t // P] = 1 - ℙ[X ≥ᵣ t // P] := by
  rw [← prob_lt_compl_ge]
  ring

theorem prob_le_monotone : X ≤ Y → t₁ ≤ t₂ → ℙ[Y ≤ᵣ t₁ // P] ≤ ℙ[X ≤ᵣ t₂ // P] := by 
  intro hxy ht 
  exact exp_monotone (rvle_monotone hxy ht)

theorem prob_lt_monotone : X ≤ Y → t₁ ≤ t₂ → ℙ[Y <ᵣ t₁ // P] ≤ ℙ[X <ᵣ t₂ // P] := by 
  intro hxy ht
  exact exp_monotone (rvlt_monotone hxy ht)

theorem prob_ge_antitone : X ≤ Y → t₁ ≤ t₂ → ℙ[Y ≥ᵣ t₁ // P] ≥ ℙ[X ≥ᵣ t₂ // P] := by 
  intro hxy ht 
  rewrite [prob_ge_of_lt,prob_ge_of_lt] 
  have := prob_lt_monotone (P := P) hxy ht 
  linarith 

theorem prob_gt_antitone : X ≤ Y → t₁ ≤ t₂ → ℙ[Y >ᵣ t₁ // P] ≥ ℙ[X >ᵣ t₂ // P] := by 
  intro hxy ht 
  rewrite [prob_gt_of_le,prob_gt_of_le] 
  have := prob_le_monotone (P := P) hxy ht 
  linarith 


------------------------------ Expectation ---------------------------

section Expectation 

variable {n : ℕ} {P : Findist n}
variable {k : ℕ} {X : FinRV n ℚ} {B : FinRV n Bool} {L : FinRV n (Fin k)}
variable  (g : Fin k → ℚ)

/-- LOTUS: The law of the unconscious statistician (or similar) -/
theorem LOTUS : 𝔼[g ∘ L // P ] = ∑ i, ℙ[L =ᵣ i // P] * (g i) :=
  by rewrite [exp_decompose (X := g ∘ L) (L := L) ]
     apply Fintype.sum_congr
     intro i
     rewrite [←indi_eq_indr]
     rewrite [←exp_cond_eq_def (X := g ∘ L) ]
     by_cases! h : ℙ[L =ᵣ i // P] = 0 
     · rw [h];  simp only [mul_zero, zero_mul]
     · rw [exp_cond_const i h ]
       ring 

theorem law_total_exp : 𝔼[𝔼[X |ᵣ L // P] // P] = 𝔼[X // P] :=
  let g i := 𝔼[X | L =ᵣ i // P]
  calc
    𝔼[𝔼[X |ᵣ L // P] // P ] = ∑ i , ℙ[ L =ᵣ i // P] * 𝔼[ X | L =ᵣ i // P ] := LOTUS g
    _ =  ∑ i , 𝔼[ X | L =ᵣ i // P ] * ℙ[ L =ᵣ i // P] := by apply Fintype.sum_congr; intro i; ring 
    _ =  ∑ i : Fin k, 𝔼[X * (𝕀 ∘ (L =ᵣ i)) // P] := by apply Fintype.sum_congr; exact fun a  ↦ exp_cond_eq_def
    _ =  ∑ i : Fin k, 𝔼[X * (L =ᵢ i) // P] := by apply Fintype.sum_congr; intro i; apply exp_congr; rw[indi_eq_indr] 
    _ = 𝔼[X // P]  := by rw [←exp_decompose]

end Expectation 

section Probability 

variable {k : ℕ}  {L : FinRV n (Fin k)}

/-- The law of total probabilities -/
theorem law_of_total_probs : ℙ[B // P] =  ∑ i, ℙ[B * (L =ᵣ i) // P]  := 
  by rewrite [prob_eq_exp_ind, rv_decompose (𝕀∘B) L, exp_additive]
     apply Fintype.sum_congr
     intro i 
     rewrite [prob_eq_exp_ind] 
     apply exp_congr
     ext ω
     by_cases h1 : L ω = i 
     repeat by_cases h2 : B ω; repeat simp [h1, h2, 𝕀, indicator ]

end Probability 

---- Prababilities and permutations 

section Probability_Permutation

variable {n : ℕ} {P : Findist n} {A B : FinRV n Bool} {X Y : FinRV n ℚ} {t : ℚ}

example (σ : Equiv.Perm (Fin n)) (f g : Fin n → ℚ) : f ⬝ᵥ g = (f ∘ σ) ⬝ᵥ (g ∘ σ) := 
  by exact Eq.symm (comp_equiv_dotProduct_comp_equiv f g σ)

example (σ : Equiv.Perm (Fin n)) : (1 : Fin n → ℚ) = (1 : Fin n → ℚ) ∘ σ := rfl

def Findist.perm (P : Findist n) (σ : Equiv.Perm (Fin n)) : Findist n where 
  p :=  P.p ∘ σ
  prob := by 
    have h1 : 1 = (1 : Fin n → ℚ) ∘ σ := rfl 
    rw [h1, comp_equiv_dotProduct_comp_equiv 1 P.p σ]
    exact P.prob
  nneg := fun ω => P.nneg (σ ω)

variable (σ : Equiv.Perm (Fin n))

theorem exp_eq_perm : 𝔼[X ∘ σ // P.perm σ] = 𝔼[X // P] := by
  unfold expect Findist.perm 
  exact (comp_equiv_dotProduct_comp_equiv P.1 X σ)

theorem prob_eq_perm : ℙ[A ∘ σ // P.perm σ] = ℙ[A // P] := by 
  have h1 : (𝕀 ∘ A ∘ σ) = (𝕀 ∘ A) ∘ σ := by rfl 
  rw [prob_eq_exp_ind, h1, exp_eq_perm, ←prob_eq_exp_ind] 
  
theorem rv_le_perm : (X ∘ σ ≤ᵣ t) = (X ≤ᵣ t) ∘ σ := by unfold FinRV.leq; grind only 

theorem rv_lt_perm : (X ∘ σ <ᵣ t) = (X <ᵣ t) ∘ σ := by unfold FinRV.lt; grind only 

theorem rv_ge_perm : (X ∘ σ ≥ᵣ t) = (X ≥ᵣ t) ∘ σ := by unfold FinRV.geq; grind only 

theorem rv_gt_perm : (X ∘ σ >ᵣ t) = (X >ᵣ t) ∘ σ := by unfold FinRV.gt; grind only 

theorem prob_le_eq_perm : ℙ[X ∘ σ ≤ᵣ t // P.perm σ] = ℙ[X ≤ᵣ t // P] := by rw [rv_le_perm, prob_eq_perm]

theorem prob_lt_eq_perm : ℙ[X ∘ σ <ᵣ t // P.perm σ] = ℙ[X <ᵣ t // P] := by rw [rv_lt_perm, prob_eq_perm]

theorem prob_ge_eq_perm : ℙ[X ∘ σ ≥ᵣ t // P.perm σ] = ℙ[X ≥ᵣ t // P] := by rw [rv_ge_perm, prob_eq_perm]

theorem prob_gt_eq_perm : ℙ[X ∘ σ >ᵣ t // P.perm σ] = ℙ[X >ᵣ t // P] := by rw [rv_gt_perm, prob_eq_perm]

end Probability_Permutation 
