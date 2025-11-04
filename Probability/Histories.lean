/-
In this file we define histories and operations that are related to them.

* Defines an MDP
* Defines a history, which is a sequence of states and actions
* Defines a histories consistent with a partial sequence of states and actions
* A general randomized history-dependent policy
* The reward and probability of the history, which is used to compute the value function
* Value function for a history as the expected reward
-/
import Mathlib.Data.Nat.Defs

import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Basic

--import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Logic.Function.Defs -- Injective

import Mathlib.Probability.ProbabilityMassFunction.Basic
--variable (α σ : Type)

import LeanMDPs.Finprob

namespace MDPs

variable {σ α : Type}
--variable [Inhabited σ] [Inhabited α] -- used to construct policies

open NNReal -- for ℝ≥0 notation
open Finprob

section Definitions

/-- Markov decision process -/
structure MDP (σ α : Type) : Type where
  /-- states -/
  S : Finset σ
  S_ne : S.Nonempty
  /-- actions  -/
  A : Finset α
  A_ne : A.Nonempty
  /-- transition probability s, a, s' -/
  P : σ → α → Δ S  -- TODO : change to S → A → Δ S
  /-- reward function s, a, s' -/
  r : σ → α → σ → ℝ -- TODO: change to S → A → S → ℝ

end Definitions

end MDPs
