import data.real.basic
import tactic.linarith
import limits

open real

local attribute [instance, priority 1000] classical.prop_decidable

noncomputable definition a : ℕ → ℝ
| 0 := 0
| (n + 1) := sqrt (1 + a n)

@[simp] lemma a_succ (n : ℕ) : a (n + 1) = sqrt (1 + a n) := begin
  unfold a,
end

@[simp] lemma a_one : a 1 = 1 :=
begin
  show sqrt (1 + 0) = 1,
  convert sqrt_one,
  simp,
end

lemma a_nonneg (n : ℕ) : 0 ≤ a n :=
begin
  induction n with d Hd,
    exact le_refl _,
  rw a_succ,
  apply sqrt_nonneg,
end

lemma a_ge_one (n : ℕ) (hn : 0 < n) : 1 ≤ a n :=
begin
  cases n with d,
  { cases hn},
  clear hn,
  induction d with m Hm,
  { -- base case
    simp
  },
  { -- inductive step
    generalize h : nat.succ m = n,
    rw h at Hm,
    show 1 ≤ a (n + 1),
    rw a_succ,
    refine le_trans (show 1 ≤ sqrt 1, by rw sqrt_one) _,
    rw sqrt_le,
    repeat {linarith},
  }
end

noncomputable def φ := (1 + sqrt 5) / 2

lemma phi_squared : φ ^ 2 = φ + 1 :=
begin
  rw pow_two,
  show (1 + sqrt 5) / 2 * ((1 + sqrt 5) / 2) = (1 + sqrt 5) / 2 + 1,
  -- First goal: get rid of divisions.
  rw div_mul_div,
  symmetry, -- kind of annoying that I have to stop my rewrite,
  rw [eq_div_iff_mul_eq, add_mul, ←mul_assoc, div_mul_cancel],
    swap, norm_num, swap, norm_num,
  -- now `ring` will do it but we need to square the sqrt(5)
  rw [mul_add, add_mul _ _ (sqrt 5), mul_self_sqrt],
    swap, norm_num,
  ring, 
end

lemma φ_squared' : φ ^ 2 = φ + 1 :=
begin
  rw φ,
  rw div_pow (_:ℝ) two_ne_zero,
  rw pow_two,
  rw add_mul_self_eq,
  rw mul_self_sqrt (show (0:ℝ) ≤ 5, by norm_num),
  ring
end

lemma φ_pos : 0 < φ :=
begin
  rw [φ, lt_div_iff, zero_mul],
    swap, norm_num,
  apply lt_add_of_lt_of_nonneg,
    norm_num,
  exact sqrt_nonneg _
end

lemma φ_nonneg : 0 ≤ φ := le_of_lt φ_pos

lemma a_lt_φ (n : ℕ) : a n < φ :=
begin
  induction n with d Hd,
    exact φ_pos,
  rw a_succ,
  rw mul_self_lt_mul_self_iff,
    swap, exact sqrt_nonneg _, swap, exact le_of_lt φ_pos,
  rw ←pow_two,
  rw sqr_sqrt,
    { rw [←pow_two,phi_squared],
      linarith
    },
    { have h : 0 ≤ a d := a_nonneg d,
      linarith,
    }
end

lemma a_mono (n : ℕ) : a n < a (n + 1) :=
begin
  rw a_succ,
  rw mul_self_lt_mul_self_iff,
    swap, exact a_nonneg _, swap, exact sqrt_nonneg _,
  rw ←pow_two (sqrt _), rw sqr_sqrt,
  { suffices : a n * (a n - 1) < 1,
      rwa [mul_sub, mul_one, sub_lt_iff_lt_add] at this,
    have h2 : 0 ≤ a n := a_nonneg n,
    cases classical.em (a n - 1 ≤ 0),
    {
      refine lt_of_le_of_lt _ (zero_lt_one),
      exact mul_nonpos_of_nonneg_of_nonpos h2 h,
    },
    { replace h := lt_of_not_ge h,
      have h3 : a n < φ := a_lt_φ n,
      have h4 : a n - 1 < φ - 1 := sub_lt_sub_right h3 _,
      refine lt_of_lt_of_le (mul_lt_mul h3 (le_of_lt h4) h φ_nonneg) _,
      apply le_of_eq,
      rw [mul_sub, ←pow_two, phi_squared],
      simp
    }
  },
  { have h : 0 ≤ a n := a_nonneg n,
    linarith,
  }
end

lemma aux_thing (c : ℕ → ℝ) (h : ∀ n, c n ≤ c (n + 1)) (m n : ℕ)
(h2 : m ≤ n) : c m ≤ c n :=
begin
  induction h2 with p Hp ih,
    refl,
  exact le_trans ih (h p),
end

lemma cgt_of_increasing_and_bounded_above (c : ℕ → ℝ)
(h1 : ∃ B, ∀ n, c n ≤ B) (h2 : ∀ n, c n ≤ c (n + 1)) :
∃ l : ℝ, M1P1.is_limit c l :=
begin
  let S := set.range c,
  let l : ℝ := Sup S,
  use l,
  have h3 : ∃ x, x ∈ S := ⟨c 0, set.mem_range_self 0⟩, 
  cases h1 with B HB,
  have h4 : ∃ (x : ℝ), ∀ (y : ℝ), y ∈ S → y ≤ x,
  { use B,
    exact λ y ⟨n, H⟩, H ▸ HB _,
  },
  intros ε Hε,
  have h5 := Sup_le S h3 h4,
    swap, exact Sup S - ε,
  have h6 : ¬(Sup S ≤ Sup S - ε),
    linarith,
  rw h5 at h6,
  simp only [not_forall] at h6,
  rcases h6 with ⟨x, ⟨N, rfl⟩, HN⟩,
  use N,
  intros n Hn,
  rw abs_lt,
  change N ≤ n at Hn,

  split,
  { have h6 := aux_thing c h2 N n Hn,
    change _ < _ - Sup S,
    linarith,
  },
  { have h7 := le_Sup S h4 ⟨n, rfl⟩,
    change _ - Sup S < _,
    linarith,
  }
end


-- lemma a_cgt : ∃ l : ℝ, M1P1.is_limit a l :=
