import data.real.basic tactic.ring

example (a b l m : ℝ) :
  abs(a + (b + (-l - m))) = abs(a + (-l + (b - m))) :=
-- by ring -- I think this used to work but now it doesn't
by congr' 1; ring
