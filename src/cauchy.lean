import limits

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

-- the maths starts here.

-- We introduce the usual mathematical notation for absolute value
local notation `|` x `|` := abs x

def is_cauchy (a : ℕ → ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε 

-- is_subsequence b a means b is a subsequence of a
def is_subsequence (b : ℕ → ℝ) (a : ℕ → ℝ) : Prop :=
∃ s : ℕ → ℕ, b = a ∘ s ∧ ∀ m : ℕ, s m < s (m + 1)

def is_monotone (b : ℕ → ℝ) : Prop :=
(∀ m, b m ≤ b (m + 1)) ∨ ∀ m, b (m + 1) ≤ b m 

theorem exists_monotone (a : ℕ → ℝ) :
∃ b : ℕ → ℝ, is_subsequence b a ∧ is_monotone b := sorry

theorem bounded_of_cauchy (a : ℕ → ℝ) : is_cauchy a → is_bounded a
:= sorry

theorem bolzano_weierstrass := sorry
