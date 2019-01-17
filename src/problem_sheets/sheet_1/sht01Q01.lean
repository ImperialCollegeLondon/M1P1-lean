-- This import gives us a working copy of the real numbers ℝ,
-- and functions such as abs : ℝ → ℝ 
import data.real.basic

-- This next import gives us several tactics of use to mathematicians:
-- (1) norm_num [to prove basic facts about reals like 2+2 = 4]
-- (2) ring [to prove basic algebra identities like (a+b)^2 = a^2+2ab+b^2]
-- (3) linarith [to prove basic inequalities like x > 0 -> x/2 > 0]
import tactic.linarith

-- These lines switch Lean into "maths proof mode" -- don't worry about them.
-- Basically they tell Lean to use the axiom of choice and the
-- law of the excluded middle, two standard maths facts.
noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

-- the maths starts here.

-- We introduce the usual mathematical notation for absolute value
local notation `|` x `|` := abs x

theorem Q1a (x y : ℝ) : | x + y | ≤ | x | + | y | :=
begin
  -- Lean's definition of abs is abs x = max (x, -x)
  -- [or max x (-x), as the computer scientists would write it]
  unfold abs,
  -- lean's definition of max a b is "if a<=b then b else a"
  unfold max,
  -- We now have a complicated statement with three "if"s in.
  split_ifs,
  -- We now have 2^3=8 goals corresponding to all the possibilities
  -- x>=0/x<0, y>=0/y<0, (x+y)>=0/(x+y)<0.
  repeat {linarith},
  -- all of them are easily solvable using the linarith tactic.
end


-- Example of how to apply this
theorem Q1h (x y z : ℝ) : | x - y | ≤ | z - y | + | z - x | :=
calc
| x - y | = | (z - y) + (x - z) | : by ring
...       ≤ | z - y | + | x - z | : by refine Q1a _ _ -- applying triangle inequality
...       = | z - y | + | -(x - z) | : by rw abs_neg -- this lemma says |-x| = |x|
...       = | z - y | + | z - x | : by simp

