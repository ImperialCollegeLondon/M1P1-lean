import limits Bolzano_Weierstrass

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

-- the maths starts here.

-- We introduce the usual mathematical notation for absolute value
local notation `|` x `|` := abs x

def is_cauchy (a : ℕ → ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε 

/- TODO: merge with monotone.lean
-- is_subsequence b a means b is a subsequence of a
def is_subsequence (b : ℕ → ℝ) (a : ℕ → ℝ) : Prop :=
∃ s : ℕ → ℕ, b = a ∘ s ∧ ∀ m : ℕ, s m < s (m + 1)

def is_monotone (b : ℕ → ℝ) : Prop :=
(∀ m, b m ≤ b (m + 1)) ∨ ∀ m, b (m + 1) ≤ b m 

theorem exists_monotone (a : ℕ → ℝ) :
∃ b : ℕ → ℝ, is_subsequence b a ∧ is_monotone b := sorry -/

theorem bounded_of_bounded_shift (a : ℕ → ℝ) (N : ℕ) :
  M1P1.is_bounded (λ k, a (N + k)) → M1P1.is_bounded a :=
nat.rec_on N (by simp only [zero_add, imp_self]) $ λ N ih ha, ih $
let ⟨M, HM⟩ := ha in ⟨max M ( |a N| ), λ y,
nat.cases_on y (le_max_right _ _) $ λ y,
le_trans (by convert HM y; simp only [nat.succ_add]) (le_max_left _ _)⟩

theorem bounded_of_cauchy (a : ℕ → ℝ) : is_cauchy a → M1P1.is_bounded a :=
λ ha, let ⟨N, hn⟩ := ha 1 zero_lt_one in bounded_of_bounded_shift a N ⟨|a N| + 1, λ k,
calc  |a (N + k)|
    ≤ |a N + (a (N + k) - a N)| : by rw add_sub_cancel'_right
... ≤ |a N| + |a (N + k) - a N| : abs_add_le_abs_add_abs _ _
... ≤ |a N| + 1 : add_le_add_left (le_of_lt $ hn _ (nat.le_add_right _ _) _ (le_refl _)) _⟩

theorem cauchy_implies_convergent (a : ℕ → ℝ) : is_cauchy a → M1P1.has_limit a :=
λ ha, let ⟨s, hsi, L, hsL⟩ := bolzano_weierstrass a (bounded_of_cauchy a ha) in ⟨L, λ ε Hε,
let ⟨N1, HN1⟩ := ha (ε/2) (half_pos Hε) in
let ⟨N2, HN2⟩ := hsL (ε/2) (half_pos Hε) in
⟨max N1 N2, λ n hn,
have hn1 : N1 ≤ n, from le_trans (le_max_left _ _) hn,
have hn2 : N2 ≤ n, from le_trans (le_max_right _ _) hn,
calc  |a n - L|
    ≤ |a n - a (s n)| + |a (s n) - L| : abs_sub_le _ _ _
... < ε/2 + ε/2 : add_lt_add (HN1 _ hn1 _ $ le_trans hn1 $ n.le_of_strictly_increasing s hsi) (HN2 _ hn2)
... = ε : add_halves ε⟩⟩
