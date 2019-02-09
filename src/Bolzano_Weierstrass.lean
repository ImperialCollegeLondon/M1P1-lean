import monotone limits

theorem bdd_above_of_is_bounded (f : ℕ → ℝ) (hfb : M1P1.is_bounded f) : bdd_above (set.range f) :=
let ⟨M, hm⟩ := hfb in ⟨M, λ y ⟨n, hn⟩, hn ▸ (abs_le.1 (hm n)).2⟩

theorem bdd_below_of_is_bounded (f : ℕ → ℝ) (hfb : M1P1.is_bounded f) : bdd_below (set.range f) :=
let ⟨M, hm⟩ := hfb in ⟨-M, λ y ⟨n, hn⟩, hn ▸ (abs_le.1 (hm n)).1⟩

theorem M1P1.is_bounded.comp {f : ℕ → ℝ} (hf : M1P1.is_bounded f) (s : ℕ → ℕ) : M1P1.is_bounded (f ∘ s) :=
let ⟨M, hm⟩ := hf in ⟨M, λ y, hm (s y)⟩

theorem increasing_bounded (f : ℕ → ℝ) (hfb : M1P1.is_bounded f) (hfi : increasing f) :
  M1P1.is_limit f (real.Sup $ set.range f) :=
begin
  intros ε Hε,
  have := mt (real.Sup_le_ub (set.range f) ⟨f 0, 0, rfl⟩) (not_le_of_lt $ sub_lt_self _ Hε),
  classical, simp only [not_forall] at this, rcases this with ⟨_, ⟨n, rfl⟩, hn⟩, use n, intros m hnm,
  rw abs_sub_lt_iff, split,
  { rw sub_lt_iff_lt_add', refine lt_of_le_of_lt _ (lt_add_of_pos_right _ Hε),
    exact real.le_Sup _ (bdd_above_of_is_bounded _ hfb) ⟨m, rfl⟩ },
  { rw sub_lt, exact lt_of_lt_of_le (not_le.1 hn) (hfi _ _ hnm) }
end

theorem decreasing_bounded (f : ℕ → ℝ) (hfb : M1P1.is_bounded f) (hfd : decreasing f) :
  M1P1.is_limit f (real.Inf $ set.range f) :=
begin
  intros ε Hε,
  have := mt (real.lb_le_Inf (set.range f) ⟨f 0, 0, rfl⟩) (not_le_of_lt $ lt_add_of_pos_right _ Hε),
  classical, simp only [not_forall] at this, rcases this with ⟨_, ⟨n, rfl⟩, hn⟩, use n, intros m hnm,
  rw abs_sub_lt_iff, split,
  { rw sub_lt_iff_lt_add', exact lt_of_le_of_lt (hfd _ _ hnm) (not_le.1 hn) },
  { rw sub_lt, refine lt_of_lt_of_le (sub_lt_self _ Hε) _,
    exact real.Inf_le _ (bdd_below_of_is_bounded _ hfb) ⟨m, rfl⟩ }
end

theorem bolzano_weierstrass (f : ℕ → ℝ) (hf : M1P1.is_bounded f) : ∃ s : ℕ → ℕ, strictly_increasing s ∧ M1P1.has_limit (f ∘ s) :=
let ⟨s, hs1, hs2⟩ := exists_monotone f in or.cases_on hs2
  (λ hsi, ⟨s, hs1, _, increasing_bounded _ (hf.comp s) (increasing_of_strictly_increasing _ hsi)⟩)
  (λ hsd, ⟨s, hs1, _, decreasing_bounded _ (hf.comp s) hsd⟩)
