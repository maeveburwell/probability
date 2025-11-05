import Probability.Probability.Prelude

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

def shrink (supp : P.supported) : Finprob :=
  {ℙ := P.ℙ.shrink, prob := P.prob.shrink supp}


-- Define an induction principle for probability spaces
-- similar  to the induction on lists, but also must argue about probability distributions

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

theorem shrink_length (supp : P.supported) : (P.shrink supp).length = P.length - 1 :=
    by  have h := Finprob.nonempty P
        simp [List.isEmpty] at h
        simp! [Finprob.shrink, Finprob.length, List.shrink, LSimplex.shrink]

theorem shrink_length_lt (supp : P.supported) : (P.shrink supp).length < P.length :=
    by rw [Finprob.shrink_length P supp]
       exact Nat.sub_one_lt_of_lt (Finprob.length_gt_zero P)

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
