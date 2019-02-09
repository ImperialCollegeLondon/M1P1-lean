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
  -- x>=0 or x<0, y>=0 or y<0, (x+y)>=0 or (x+y)<0.
  repeat {linarith},
  -- all of them are easily solvable using the linarith tactic.
end

-- We can solve the remaining parts using part (a).
theorem Q1b (x y : ℝ) : |x + y| ≥ |x| - |y| :=
begin
  -- Apply Q1a to x+y and -y, then follow your nose.
  have h := Q1a (x + y) (-y),
  simp at h,
  linarith,
end

theorem Q1c (x y : ℝ) : |x + y| ≥ |y| - |x| :=
begin
  -- Apply Q1a to x+y and -x, then follow your nose.
  have h := Q1a (x + y) (-x),
  simp at h,
  linarith,
end

theorem Q1d (x y : ℝ) : |x - y| ≥ | |x| - |y| | :=
begin
  -- Lean prefers ≤ to ≥
  show _ ≤ _,
  -- for this one we need to apply the result that |X| ≤ B ↔ -B ≤ X and X ≤ B 
  rw abs_le,
  -- Now we have two goals:
  -- first -|x - y| ≤ |x| - |y|
  -- and second |x| - |y| ≤ |x - y|.
  -- So we need to split.
  split,
  { -- -|x - y| ≤ |x| - |y|
    have h := Q1a (x - y) (-x),
    simp at *,
    linarith },
  { -- |x| - |y| ≤ |x - y|
    have h := Q1a (x - y) y,
    simp at *,
    linarith}
end

theorem Q1e (x y : ℝ) : |x| ≤ |y| + |x - y| :=
begin
  have h := Q1a y (x - y),
  simp * at *,
end

theorem Q1f (x y : ℝ) : |x| ≥ |y| - |x - y| :=
begin
  have h := Q1a (x - y) (-x),
  simp * at *,
  linarith,
end

theorem Q1g (x y z : ℝ) : |x - y| ≤ |x - z| + |y - z| :=
begin
  have h := Q1a (x - z) (z - y),
  -- Lean needs more hints with this one.
  -- First let's change that y - z into z - y,
  rw ←abs_neg (y - z),
  -- now get everything into some sort of normal form
  simp * at *,
  -- unfortunately Lean didn't yet simplify x + (z + (-y + -z))
  -- The "convert" tactic says "OK the goal should equal this, so
  -- replace the goal with all the bits that aren't exactly equal"
  convert h,
  -- now we need to prove -y = z + (-y + -z)!
  ring,
end
