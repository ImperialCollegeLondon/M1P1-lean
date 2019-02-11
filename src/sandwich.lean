-- begin header
import limits

namespace M1P1
-- end header

/- Section
The sandwich theorem
-/

/- Sub-section
Introdiction
-/

/-
The sandwich theorem, or squeeze theorem, for sequences is the statement that if $(a_n)$, $(b_n)$, and $(c_n)$ are three real-valued sequences satisfying $a_n≤ b_n≤ c_n$ for all $n$, and if furthermore $a_n→ℓ$ and $c_n→ℓ$, then $b_n→ℓ$. The idea of the proof is straightforward -- if we want to ensure that $|b_n-ℓ|<ε$ then it suffices to show that $|a_n-ℓ|<ε$ and $|c_n-ℓ|<ε$. 
-/

/- Theorem
If $(a_n)$, $(b_n)$, and $(c_n)$ are three real-valued sequences satisfying $a_n ≤ b_n ≤ c_n$ for all $n$, and if furthermore $a_n→ℓ$ and $c_n→ℓ$, then $b_n→ℓ$.
-/
theorem sandwich (a b c : ℕ → ℝ)
  (l : ℝ) (ha : is_limit a l) (hc : is_limit c l) 
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : is_limit b l :=
begin
  -- We need to show that for all $ε>0$ there exists $N$ such that $n≥N$ implies $|b_n-ℓ|<ε$. So choose ε > 0.
  intros ε Hε,
  -- we now need an $N$. As usual it is the max of two other N's, one coming from $(a_n)$ and one from $(c_n)$. Choose $N_a$ and $N_c$ such that $|aₙ - l| < ε$ for $n ≥ Na$ and $|cₙ - l| < ε$ for $n ≥ Nc$.
  cases ha ε Hε with Na Ha,
  cases hc ε Hε with Nc Hc,
  -- Now let $N$ be the max of $N_a$ and $N_c$; we claim that this works.
  let N := max Na Nc,
  use N,
  -- Note that N ≥ Na and N ≥ Nc,
  have HNa : Na ≤ N := by obvious_ineq,  
  have HNc : Nc ≤ N := by obvious_ineq,
  -- so for all n ≥ N, 
  intros n Hn,
  -- we have $n≥ N_a$ and $n\geq N_c$, so $aₙ ≤ bₙ ≤ cₙ$, and $|aₙ - l|, |bₙ - l|$ are both less than $\epsilon$.
  have h1 : a n ≤ b n := hab n,
  have h2 : b n ≤ c n := hbc n,
  have h3 : |a n - l| < ε := Ha n (le_trans HNa Hn),
  have h4 : |c n - l| < ε := Hc n (le_trans HNc Hn),
  -- The result now follows easily from these inequalities (as $l-ε<a_n≤b_n≤c_n<l+ε$). 
  revert h3,revert h4,
  unfold abs,unfold max,
  split_ifs;intros;linarith,
end

/-
Note that Lean finds the last line of the proof automatically -- we do not need to explicitly tell it the inequality argument.
-/
end M1P1
