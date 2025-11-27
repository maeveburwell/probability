/-
In this file we define histories and operations that are related to them.

* Defines an MDP
* Defines a history, which is a sequence of states and actions
* Defines a histories consistent with a partial sequence of states and actions
* A general randomized history-dependent policy
* The reward and probability of the history, which is used to compute the value function
* Value function for a history as the expected reward
-/
import Mathlib.Data.Nat.Basic

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

import Probability.Probability.Basic

namespace MDPs

section Definitions

open Findist

/-- Markov decision process -/
structure MDP : Type where
  /-- states -/
  S : ℕ
  S_ne : 0 < S
  /-- actions  -/
  A : ℕ
  A_ne : 0 < A
  /-- transition probability s, a, s' -/
  P : Fin S → Fin A → Δ S
  /-- reward function s, a, s' -/
  r : Fin S → Fin A → Fin S → ℝ

variable (M : MDP)

def MDP.maxS : Fin M.S := ⟨M.S-1, by simp [M.S_ne]⟩
def MDP.maxA : Fin M.A := ⟨M.A-1, by simp [M.A_ne]⟩

example :  ∀ x ∈ Finset.range n, x < n := fun x y ↦ Finset.mem_range.mp y 

/-- Set of all states -/
def MDP.setS : Finset (Fin M.S) := Finset.attachFin (Finset.range M.S) (fun _ h ↦ Finset.mem_range.mp h)
/-- Set of all actions -/
def MDP.setA : Finset (Fin M.A) := Finset.attachFin (Finset.range M.A) (fun _ h ↦ Finset.mem_range.mp h)


end Definitions

variable {M : MDP}

section Histories

/-- Represents a history. The state is type ℕ and action is type ℕ. -/
inductive Hist (M : MDP)  : Type where
  | init : Fin M.S → Hist M
  | foll : Hist M → Fin M.A → Fin M.S → Hist M

/-- Coerces a single state to a history of length 0 -/
instance : Coe (Fin M.S) (Hist M) where
  coe s := Hist.init s

/-- The length of the history is the number of actions it contains -/
def Hist.length : Hist M → ℕ
  | init _ => 0
  | Hist.foll h _ _ => 1 + length h

/-- Subtype representing nonempty histories -/
abbrev HistNE (m : MDP) : Type := {h : Hist m // h.length ≥ 1}
-- TODO: Why do we need this?

/-- Returns the last state of the history -/
def Hist.last : Hist M → Fin M.S
  | init s => s
  | Hist.foll _ _ s => s

/-- Appends the state and action to the history --/
def Hist.append (h : Hist M) (as : Fin M.A × Fin M.S) : Hist M := h.foll as.1 as.2

def Hist.one (s₀ : Fin M.S) (a : Fin M.A) (s : Fin M.S) : Hist M := (Hist.init s₀).foll a s

/-- Return the prefix of hist of length k -/
def Hist.prefix (k : ℕ) (h : Hist M) : Hist M :=
    match h with
      | Hist.init s => Hist.init s
      | Hist.foll hp a s =>
        if hp.length + 1 ≤ k then hp.foll a s
        else hp.prefix k


def MDP.tuple2hist : Hist M × (Fin M.A) × (Fin M.S) → HistNE M
  | ⟨h, as⟩ => ⟨h.append as, Nat.le.intro rfl⟩

def MDP.hist2tuple : HistNE M → Hist M × (Fin M.A) × (Fin M.S) 
  | ⟨Hist.foll h a s, _ ⟩ => ⟨h, a, s⟩

open Function 

-- mapping between tuples and histories are injective

lemma linv_hist2tuple_tuple2hist : LeftInverse M.hist2tuple M.tuple2hist := fun _ ↦ rfl
lemma inj_tuple2hist_l1 : Injective M.tuple2hist  := LeftInverse.injective linv_hist2tuple_tuple2hist
lemma inj_tuple2hist : Injective (Subtype.val ∘ M.tuple2hist)  := Injective.comp (Subtype.val_injective) inj_tuple2hist_l1

def emb_tuple2hist_l1 : Hist M × (Fin M.A) × (Fin M.S) ↪ HistNE M := ⟨M.tuple2hist, inj_tuple2hist_l1⟩
def emb_tuple2hist : Hist M × (Fin M.A) × (Fin M.S) ↪ Hist M  := ⟨λ x ↦  M.tuple2hist x, inj_tuple2hist⟩

--- state
def state2hist (s : Fin M.S) : Hist M := Hist.init s
def hist2state : Hist M → (Fin M.S) 
    | Hist.init s => s 
    | Hist.foll _ _ s => s
    
lemma linv_hist2state_state2hist : LeftInverse (hist2state (M:=M)) state2hist := fun _ => rfl
lemma inj_state2hist : Injective (state2hist (M:=M)) := 
                     LeftInverse.injective linv_hist2state_state2hist
                     
def state2hist_emb : (Fin M.S) ↪ Hist M := ⟨state2hist, inj_state2hist⟩

-- TODO: we probably do not need this function 
/-- Checks if the first hist is the prefix of the second hist. -/
def isprefix : Hist M → Hist M → Bool 
    | Hist.init s₁, Hist.init s₂ => s₁ = s₂
    | Hist.init s₁, Hist.foll hp _ _ => isprefix (Hist.init s₁) hp 
    | Hist.foll _ _ _, Hist.init _ => False
    | Hist.foll h₁ a₁ s₁', Hist.foll  h₂ a₂ s₂' => 
        if h₁.length > h₂.length then
            False
        else if h₁.length < h₂.length then
            let pre := Hist.foll h₁ a₁ s₁' 
            isprefix pre h₂
        else
            (a₁ = a₂) ∧ (s₁' = s₂') ∧ (isprefix h₁ h₂)

/-- All histories that follow h for t decisions -/
def Histories (h : Hist M) : ℕ → Finset (Hist M) 
    | Nat.zero => {h}
    | Nat.succ t => ((Histories h t) ×ˢ M.setA ×ˢ M.setS).map emb_tuple2hist

abbrev ℋ : Hist M → ℕ → Finset (Hist M) := Histories

theorem hist_lenth_eq_horizon (h : Hist M) (t : ℕ): ∀ h' ∈ (ℋ h t), h'.length = h.length + t := sorry

/-- All histories of a given length  -/
def HistoriesHorizon : ℕ → Finset (Hist M)
  | Nat.zero => M.setS.map state2hist_emb 
  | Nat.succ t => ((HistoriesHorizon t) ×ˢ M.setA ×ˢ M.setS).map emb_tuple2hist


#synth SProd (Finset ℕ) (Finset ℕ) (Finset (ℕ × ℕ))
#check Fintype

abbrev ℋₜ : ℕ → Finset (Hist M) := HistoriesHorizon

--theorem Histories



end Histories

end MDPs
