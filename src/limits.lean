/- limits.lean

Limits of sequences.

Part of the M1P1 Lean project.

This file contains the basic definition of the limit of a sequence, and
proves basic properties about it.

Currently it's just the proof that a sequence has at most one limit.



-/

-- The import below gives us a working copy of the real numbers ℝ,
-- and functions such as abs : ℝ → ℝ 
import data.real.basic

-- This next import gives us several tactics of use to mathematicians:
-- (1) norm_num [to prove basic facts about reals like 2+2 = 4]
-- (2) ring [to prove basic algebra identities like (a+b)^2 = a^2+2ab+b^2]
-- (3) linarith [to prove basic inequalities like x > 0 -> x/2 > 0]
import tactic.linarith

-- These lines switch Lean into "maths proof mode" -- don't worry about them.
-- Basically they tell Lean to use the axiom of choice and the
-- law of the excluded middle, two standard maths facts which we
-- assume all the time in maths, usually without comment. 
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

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
  -- Each case is trivial, and the `linarith` tactic solves it.
  repeat {linarith},
end

-- The main work is here. We show that if a sequence has two limits l and m
-- with l < m then we have a contradiction.
-- The reason I'm doing this case first (rather than l ≠ m) is that I don't understand
-- how to use Lean's "WLOG" tactic!
lemma limits_aux (a : ℕ → ℝ) (l m : ℝ) (hl : is_limit a l)
(hm : is_limit a m) (hlm : l < m) : false :=
begin
  let ε := (m - l) / 2, -- guaranteed positive! linarith can check this.
  have Hε : ε > 0 := by show (m - l) / 2 > 0; linarith,
  cases hl ε Hε with Nl HNl, -- use definition of limit
  cases hm ε Hε with Nm HNm,
  -- so now
  -- HNl : ∀ (n : ℕ), n ≥ Nl → |a n - l| < ε,
  -- HNm : ∀ (n : ℕ), n ≥ Nm → |a n - m| < ε
  let N := max Nl Nm,
  have this : | a N - l| < ε,
  -- need to remind Lean that N ≥ Nl!
  { apply HNl,
    show max Nl Nm ≥ Nl,
    apply le_max_left
  },
  -- similarly N ≥ Nm.
  have that : | a N - m| < ε,
  { apply HNm,
    show max Nl Nm ≥ Nm,
    apply le_max_right
  },
  -- So now a basic calculation shows 2ε < 2ε. 
  -- Let's show to do this in Lean.
  have theother : 2 * ε < 2 * ε,
    calc 2 * ε = 2 * ((m - l) / 2) : by refl -- i.e. by definition
    ...        = m - l : by ring -- "ring" does the algebra for you
    ...        ≤ | m - l | : le_abs_self _ -- this low-level theorem `le_abs-self` is a proof that x ≤ |x|.
    ...        ≤ |a N  - l| + |a N - m| : triangle' _ _ _ -- our earlier lemma
    ...        < ε + ε : by linarith -- easy inequality argument
    ...        = 2 * ε : by ring, -- easy algebraic argument
  -- Now we need to get a contradiction from this
  linarith -- it's an easy inequality argument
end

-- Now the main theorem. By the previous lemma we can't have l < m or m < l so we must have l = m
theorem limits_are_unique (a : ℕ → ℝ) (l m : ℝ) (hl : is_limit a l)
(hm : is_limit a m) : l = m :=
begin
  -- apply previous lemma twice
  have H1 : ¬ (l < m)  := limits_aux a l m hl hm,  
  have H2 : ¬ (m < l) := limits_aux a m l hm hl,
  -- now use our inequality tactic.
  linarith
end
