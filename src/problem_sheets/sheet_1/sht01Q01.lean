import data.real.basic
import tactic.linarith

noncomputable theory

local notation `|` x `|` := abs x


theorem Q1a (x y : ℝ) : | x + y | ≤ | x | + | y | :=
begin
  unfold abs,
  unfold max,
  split_ifs,
  repeat {linarith},
end

-- cheat proof
theorem Q1h' (x y z : ℝ) : | x - y | ≤ | z - y | + | z - x | :=
begin
  let X := Q1a,
  unfold abs,
  unfold max,
  split_ifs,
  repeat {linarith},
end

theorem Q1h (x y z : ℝ) : | x - y | ≤ | z - y | + | z - x | :=
calc
| x - y | = | (z - y) + (x - z) | : by ring
...       ≤ | z - y | + | x - z | : Q1a _ _
...       = | z - y | + | -(x - z) | : by rw abs_neg
...       = | z - y | + | z - x | : by simp

