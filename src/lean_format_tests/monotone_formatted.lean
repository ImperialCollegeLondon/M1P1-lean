-- begin header
import tactic.linarith
import data.real.basic

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

local notation `|` x `|` := abs x
-- end header

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
/-
We are going to show that any sequence contains either a strictly increasing subsequence,
or a decreasing sequence [Does this have a name?]. The strategy of the proof is to
consider so-called peaks of the sequence. A *peak* of a sequence $(a_n)$ is an index
$i∈ℕ$ such that $a_i$ is at least as large as subsequent members of the sequence.
-/
/- Definition
A *peak* of a sequence $(a_n)$ is $i∈ℕ$ such that $∀ j≥ i, $a_j≤ a_i$.
-/
def is_peak (a : ℕ → ℝ) (i : ℕ) : Prop :=
∀ j, i ≤ j → a j ≤ a i
/-
For any sequence, consider the set of peaks. It is clearly either finite or infinite.
Let us formally state this in a more convenient form.
-/
/- Lemma
If $(a_n)$ is a sequence, then either there exists $N∈ℕ$ such that all peak $i$
of $(a_n)$ satisfy $i≤N$, or for all $N∈ℕ$ there exists a peak $i$ of $(a_n)$ with $i>N$.
-/
lemma finite_or_infinite_peaks (a : ℕ → ℝ) :
(∃ N, ∀ i, is_peak a i → i ≤ N) ∨ (∀ N, ∃ i, is_peak a i ∧ i > N) :=
by simpa [not_forall] using classical.em (∃ N, ∀ i, is_peak a i → i ≤ N)

/- Lemma
If there are infinitely many peaks for a sequence $(a_n)$, then the peaks
form a decreasing subsequence.
-/
lemma decreasing_subsequence_of_infinite_peaks (a : ℕ → ℝ) 
(h : ∀ N, ∃ i, is_peak a i ∧ i > N) :
∃ b : ℕ → ℝ, is_subsequence a b ∧ is_strictly_decreasing b :=
begin
  choose f hf using h,
  let k : ℕ → ℕ := λ n, nat.rec_on n (f 0) (λ n kn, f kn),
  use (λ n, a (k n)),  
  split,
  { use k,
    split,swap,intro,refl,
    sorry },
  { 
    sorry },
end

