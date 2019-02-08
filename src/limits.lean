/- limits.lean

Limits of sequences.

Part of the M1P1 Lean project.

This file contains the basic definition of the limit of a sequence, and
proves basic properties about it.

It is full of comments in an attempt to make it more comprehensible to
mathematicians with little Lean experience, although by far the best
way to understand what is going on is to open the file within Lean 3.4.2
so you can check out the goal at each line -- this really helps understanding.
-/

-- The import below gives us a working copy of the real numbers ℝ,
-- and functions such as abs : ℝ → ℝ 
import data.real.basic

-- This import has addition of functions, which we need for sums of limits.
import algebra.pi_instances

-- This next import gives us several tactics of use to mathematicians:
-- (1) norm_num [to prove basic facts about reals like 2+2 = 4]
-- (2) ring [to prove basic algebra identities like (a+b)^2 = a^2+2ab+b^2]
-- (3) linarith [to prove basic inequalities like x > 0 -> x/2 > 0]
import tactic.linarith
import topology.basic
import analysis.exponential

-- These lines switch Lean into "maths proof mode" -- don't worry about them.
-- Basically they tell Lean to use the axiom of choice and the
-- law of the excluded middle, two standard maths facts which we
-- assume all the time in maths, usually without comment. 
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

-- Let's also put things into an M1P1 namespace so we can define
-- stuff which is already defined in mathlib without breaking anything.
namespace M1P1

-- the maths starts here.

-- We introduce the usual mathematical notation for absolute value
local notation `|` x `|` := abs x

-- We model a sequence a₀, a₁, a₂,... of real numbers as a function
-- from ℕ := {0,1,2,...} to ℝ, sending n to aₙ . So in the below
-- definition of the limit of a sequence, a : ℕ → ℝ is the sequence.

-- We first formalise the definition of "aₙ → l as n → ∞"
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

-- A sequence converges if and only if it has a limit. The difference
-- with this definition is that we don't specify the limit, we just
-- claim that it exists.
definition has_limit (a : ℕ → ℝ) : Prop := ∃ l : ℝ, is_limit a l

-- We now start on the proof of the theorem that if a sequence has
-- two limits, they are equal. We start with a lemma.

theorem triangle' (x y z : ℝ) : | x - y | ≤ | z - y | + | z - x | :=
begin
  -- See the solution to sheet 1 Q1a for a more detailed explanation of this argument.
  -- We start by unfolding the definitions.
  unfold abs, unfold max,
  -- The value of | x - y | depends on whether x - y ≥ 0 or < 0. 
  -- The `split_ifs` tactic splits into these 8 = 2^3 cases
  split_ifs,
  -- Each case is trivial by easy inequality arguments, and the `linarith`
  -- tactic solves them all.
  repeat {linarith},
end

-- We're ready to prove the theorem.
theorem limits_are_unique (a : ℕ → ℝ) (l m : ℝ) (hl : is_limit a l)
(hm : is_limit a m) : l = m :=
begin
  -- WLOG l ≤ m.
  wlog h : l ≤ m, 
  -- We're trying to prove l = m, so it suffices to prove l < m is false.
  suffices : ¬ (l < m),
    linarith,
  -- don't need h any more
  clear h,
  -- Let's prove it by contradiction. So let's assume l < m.
  intro hlm,
  -- Our goal is now "⊢ false" and hlm is the assumption l < m.
  -- Situation so far: aₙ → l, aₙ → m, hlm is the assumption l < m
  -- and we're looking for a contradiction.
  let ε := (m - l) / 2, -- This is a standard trick.
  -- First note that ε is positive, because l > m.
  have Hε : ε > 0 := by {show (m - l) / 2 > 0, linarith},
  -- Because aₙ → l, there exists N₁ such that n ≥ N₁ → |aₙ - l| < ε 
  cases hl ε Hε with N₁ HN₁,
  -- Because bₙ → m, there exists N₂ such that n ≥ N₂ → |bₙ - m| < ε 
  cases hm ε Hε with N₂ HN₂,
  -- The trick is to let N be the max of N₁ and N₂
  let N := max N₁ N₂,
  -- Now clearly N ≥ N₁...
  have H₁ : N₁ ≤ N := le_max_left _ _,
  -- ... so |a_N - l| < ε
  have Ha : | a N - l| < ε := HN₁ N H₁,
  -- similarly N ≥ N₂...
  have H₂ : N₂ ≤ N := le_max_right _ _,
  -- ... so |a_N - m| < ε too
  have H₂ : | a N - m| < ε := HN₂ N H₂,
  -- So now a basic calculation shows 2ε < 2ε. Let's go through it.
  have weird : 2 * ε < 2 * ε,
    calc 2 * ε = 2 * ((m - l) / 2) : by refl -- by definition
                 -- and this is obviously m - l
    ...        = m - l : by ring
                 -- which is at most its own absolute value
    ...        ≤ | m - l | : le_abs_self _
                 -- and now use the triangle inequality
    ...        ≤ |a N  - l| + |a N - m| : triangle' _ _ _
                 -- and stuff we proved already
    ...        < ε + ε : by linarith
                 -- to deduce this is less than 2ε
    ...        = 2 * ε : by ring,
  -- That's the contradiction we seek!
  linarith -- (it's an easy inequality argument)
end

-- We now prove that if aₙ → l and bₙ → m then aₙ + bₙ → l + m.
theorem tendsto_add (a : ℕ → ℝ) (b : ℕ → ℝ) (l m : ℝ)
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) :=
begin
  -- let epsilon be a positive real
  intros ε Hε,
  -- We now need to come up with N such that n >= N implies
  -- |aₙ + bₙ - (l + m)| < ε.
  -- Well, note first that epsilon / 2 is also positive.
  have Hε2 : ε / 2 > 0 := by linarith,
  -- Choose large M₁ such that n ≥ M₁ implies |a n - l| < ε /2
  cases (h1 (ε / 2) Hε2) with M₁ HM₁,
  -- similarly choose M₂ for the b sequence. 
  cases (h2 (ε / 2) Hε2) with M₂ HM₂,
  -- let N be the max of M1 and M2
  let N := max M₁ M₂,
  -- and let's use that 
  use N,
  -- Of course N ≥ M₁ and N ≥ M₂
  have H₁ : N ≥ M₁ := le_max_left _ _,
  have H₂ : N ≥ M₂ := le_max_right _ _,
  -- Now say n ≥ N.
  intros n Hn,
  -- Then obviously n ≥ M₁...
  have Hn₁ : n ≥ M₁ := by linarith,
  -- ...so |aₙ - l| < ε /2
  have H3 : |a n - l| < ε / 2 := HM₁ n Hn₁,
  -- and similarly n ≥ M₂, so |bₙ - l| < ε / 2
  have H4 : |b n - m| < ε / 2 := HM₂ n (by linarith),
  -- And now what we want (|aₙ + bₙ - (l + m)| < ε) 
  -- follows from a calculation.
                               -- First do some obvious algebra
  calc |(a + b) n - (l + m)| = |(a n - l) + (b n - m)| : by ring
                               -- now use the triangle inequality
  ...                        ≤ |(a n - l)| + |(b n - m)| : abs_add _ _
                               -- and our assumptions
  ...                        < ε / 2 + ε / 2 : by linarith 
                               -- and a bit more algebra
  ...                        = ε : by ring
end

end M1P1
