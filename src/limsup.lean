-- amazing theory of limsups

import limits

namespace M1P1

/- Section
Sequences, subsequences, and monotonic subsequences.
-/

/- Sub-section
Definitions
-/

/-
We model a sequence $a₀, a₁, a₂, \dots$ of real numbers as a function
from $ℕ := \{0,1,2,\dots\}$ to $ℝ$, sending $n$ to $a_n$. We sometimes write such
a sequence as $(a_n)_{n≥0}$ or just $(a_n)$.
-/

/- Definition
A sequence $(a_n)$ is *increasing* if forall $n∈ℕ$ we have $a_n≤a_{n+1}$. Note that equality
is allowed here -- so for example the sequence $3, 3, 3, 3, …$ is increasing. A sequence is
*strictly increasing* if for all $n∈ℕ$ we have $a_n<a_{n+1}$; constant sequences
are not strictly increasing. 
-/
def is_increasing {X : Type*} [has_le X] (a : ℕ → X) : Prop :=
∀ n : ℕ, a n ≤ a (n + 1)
def is_strictly_increasing {X : Type*} [has_lt X] (a : ℕ → X) : Prop :=
∀ n : ℕ, a n < a (n + 1)
/- Definition
Similarly a sequence $(a_n)$ is *decreasing* if $∀ n∈ℕ, a_{n+1}≤ a_n$ and is
*strictly decreasing* if $∀ n∈ℕ, a_{n+1}<a_n$.
-/
def is_decreasing {X : Type*} [has_le X] (a : ℕ → X) : Prop :=
∀ n : ℕ, a (n + 1) ≤ a n
def is_strictly_decreasing {X : Type*} [has_lt X] (a : ℕ → X) : Prop :=
∀ n : ℕ, a (n + 1) < a n
/-
A *subsequence* of a sequence $(a_n)$ is a sequence $(b_m)$ of the form
$a_{k_0}$, $a_{k_1}$, $a_{k_2}$, where the indices $0≤ k_0<k_1<k_2<…$ are strictly increasing.
-/
def is_subsequence {X : Type*} (a : ℕ → X) (b : ℕ → X) :=
∃ k : ℕ → ℕ, is_strictly_increasing k ∧ ∀ n, a (k n) = b n

definition is_limit_point (a : ℕ → ℝ) (l : ℝ) :=
∃ (b : ℕ → ℝ), is_subsequence a b ∧ is_limit b l


end M1P1
