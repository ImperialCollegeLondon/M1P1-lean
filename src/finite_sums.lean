import data.fintype -- for finset and finset.sum
import data.real.basic

universe u

variables {R : Type u} [add_comm_monoid R]

-- my_sum_to_n eats a summand f(n) and returns the function sending t to f(0)+f(1)+...+f(t-1).
-- Chris says use finsets.
definition sum_to_n_minus_one (summand : ℕ → R) : ℕ → R :=
λ n, (finset.range n).sum summand

--#reduce sum_to_n_minus_one (λ n, n ^ 2) 1000000

#check finset.range 4 -- finset ℕ

#check @finset.sum 

definition sum_from_a_to_b_minus_one (summand : ℕ → R) (a b : ℕ) : R :=
(finset.Ico a b).sum summand

#eval sum_from_a_to_b_minus_one (id) 4 7

theorem finset.polygon {α : Type*} [decidable_eq α] (X : finset α) (summand : α → ℝ) :
abs (X.sum summand) ≤ X.sum (λ a, abs (summand a)) :=
begin
  apply finset.induction_on X,
  { simp },
  { intro a,
    intro s,
    intro hs,
    intro ih,
    sorry
  }
end