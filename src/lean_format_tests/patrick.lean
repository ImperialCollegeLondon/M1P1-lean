-- begin header
import tactic.linarith
import data.real.basic
import algebra.pi_instances
import data.set.function
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

-- We introduce the usual mathematical notation for absolute value
local notation `|` x `|` := abs x
-- end header

/- Section
Limits of sequences
-/

/- Sub-section
Basic definitions
-/

/-
In this file, we introduce limits of sequences of real numbers.

We model a sequence $a₀, a₁, a₂, \dots$ of real numbers as a function
from $ℕ := \{0,1,2,\dots\}$ to $ℝ$, sending $n$ to $a_n$. So in the below
definition of the limit of a sequence, $a : ℕ → ℝ$ is the sequence.
-/

/- Definition
A sequence $a$ converges to a real number $l$ if, for all positive
$ε$, there is some $N$ such that, for every $n ≥ N$, $|a_n - l| < ε$.
-/
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

/- Definition
A sequence converges if and only if it has a limit.
-/
definition has_limit (a : ℕ → ℝ) : Prop := ∃ l : ℝ, is_limit a l

/-
The difference between the above definition and the preceding one is that we
don't specify the limit, we just claim that it exists.
-/

/- Sub-section
Basic lemmas
-/

/- Lemma
The constant sequence with value $a$ converges to $a$.
-/
lemma tendsto_const (a : ℝ) : is_limit (λ n, a) a :=
begin
  -- Let $ε$ be any positive real number.
  intros ε εpos,
  -- We choose $N = 0$ in the definition of a limit,
  use 0,
  -- and observe that, for every $n ≥ N$, |a - a| < ε
  intros n _,
  simpa [sub_self] using εpos
end

/-
We will need an easy reformulation of the limit definition
-/
/- Lemma
A sequence $a_n$ converges to a number $l$ if and only if the sequence
$a_n - l$ converges to zero.
-/
lemma tendsto_iff_sub_tendsto_zero {a : ℕ → ℝ} {l : ℝ} :
  is_limit (λ n, a n - l) 0 ↔ is_limit a l :=
begin
  -- We need to prove both implications, but both proofs are the same.
  split ; 
  { -- We assume the premise, and consider any positive $ε$.
    intros h ε εpos,
    -- By the premise specialized to our $ε$, we get some $N$,
    rcases h ε εpos with ⟨N, H⟩,
    -- and use that $N$ to prove the other condition
    use N,
    -- which is immediate.
    intros n hn,
    simpa using H n hn }
end

/- 
In the definition of a limit, the final ε can be replaced 
by a constant multiple of ε. We could assume this constant is positive
but we don't want to deal with this when applying the lemma.
-/
/- Lemma
Let $a$ be a sequence. In order to prove that $a$ converges to some limit 
$l$, it is sufficient to find some number $K$ such that,
for all $ε > 0$, there is some $N$ such that, for all $n ≥ N$, 
$|a_n - l| < Kε$.
-/
lemma tendsto_of_mul_eps (a : ℕ → ℝ) (l : ℝ) (K : ℝ)
  (h : ∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < K*ε) : is_limit a l :=
begin
  -- Let $ε$ be any positive number.
  intros ε εpos,
  -- $K$ is either non positive or positive
  cases le_or_gt K 0 with Knonpos Kpos,
  { -- If $K$ is non positive then our assumed bound quickly
    -- gives a contradiction. 
    exfalso,
    -- Indeed we can apply our assumption to $ε = 1$ to get $N$ such that
    -- for all $n ≥ N$, $|a n - l| < K * 1$ 
    rcases h 1 (by linarith) with ⟨N, H⟩,
    -- in particular this holds when $n = N$
    specialize H N (by linarith),
    -- but $|a N - l| ≥ 0$ so we get a contradiction.
    have : |a N - l| ≥ 0, from abs_nonneg _,
    linarith },
  { -- Now assume $K$ is positive. Our assumption gives $N$ such that,
    -- for all $n ≥ N$, $|a n - l| < K * (ε / K)$
    rcases h (ε/K) (div_pos εpos Kpos) with ⟨N, H⟩,
    -- we can simplify that $K (ε / K)$ and we are done.
    rw mul_div_cancel' _ (ne_of_gt Kpos) at H,
    tauto }
end
