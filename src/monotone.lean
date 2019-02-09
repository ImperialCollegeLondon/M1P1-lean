import tactic.interactive algebra.order data.finset

universes u v

section monotone

def increasing {α : Type u} [has_le α] {β : Type v} [has_le β] (f : α → β) : Prop :=
∀ x y, x ≤ y → f x ≤ f y

def decreasing {α : Type u} [has_le α] {β : Type v} [has_le β] (f : α → β) : Prop :=
∀ x y, x ≤ y → f y ≤ f x

def strictly_increasing {α : Type u} [has_lt α] {β : Type v} [has_lt β] (f : α → β) : Prop :=
∀ x y, x < y → f x < f y

def strictly_decreasing {α : Type u} [has_lt α] {β : Type v} [has_lt β] (f : α → β) : Prop :=
∀ x y, x < y → f y < f x

theorem increasing_of_strictly_increasing {α : Type u} [partial_order α] {β : Type v} [preorder β]
  (f : α → β) (hf : strictly_increasing f) : increasing f :=
λ x y hxy, or.cases_on (lt_or_eq_of_le hxy) (λ hxy, le_of_lt $ hf x y hxy) (λ hxy, hxy ▸ le_refl _)

theorem decreasing_of_strictly_decreasing {α : Type u} [partial_order α] {β : Type v} [preorder β]
  (f : α → β) (hf : strictly_decreasing f) : decreasing f :=
λ x y hxy, or.cases_on (lt_or_eq_of_le hxy) (λ hxy, le_of_lt $ hf x y hxy) (λ hxy, hxy ▸ le_refl _)

theorem increasing_of_nat {α : Type u} [preorder α] (f : ℕ → α) (hf : ∀ n, f n ≤ f (n + 1)) : increasing f :=
λ x y hxy, nat.less_than_or_equal.rec_on hxy (le_refl _) $ λ n hn ih, le_trans ih $ hf n

theorem strictly_increasing_of_nat {α : Type u} [preorder α] (f : ℕ → α) (hf : ∀ n, f n < f (n + 1)) : strictly_increasing f :=
λ x y hxy, nat.less_than_or_equal.rec_on hxy (hf x) $ λ n hn ih, lt_trans ih $ hf n

theorem decreasing_of_nat {α : Type u} [preorder α] (f : ℕ → α) (hf : ∀ n, f (n + 1) ≤ f n) : decreasing f :=
λ x y hxy, nat.less_than_or_equal.rec_on hxy (le_refl _) $ λ n hn ih, le_trans (hf n) ih

theorem strictly_decreasing_of_nat {α : Type u} [preorder α] (f : ℕ → α) (hf : ∀ n, f (n + 1) < f n) : strictly_decreasing f :=
λ x y hxy, nat.less_than_or_equal.rec_on hxy (hf x) $ λ n hn ih, lt_trans (hf n) ih

end monotone

variables {α : Type u} [decidable_linear_order α]

theorem exists_monotone (f : ℕ → α) :
  ∃ s : ℕ → ℕ, strictly_increasing s ∧ (strictly_increasing (f ∘ s) ∨ decreasing (f ∘ s)) :=
begin
  classical,
  by_cases h1 : ∃ s : ℕ → ℕ, strictly_increasing s ∧ strictly_increasing (f ∘ s),
  { rcases h1 with ⟨s, hs1, hs2⟩, exact ⟨s, hs1, or.inl $ hs2⟩ },
  simp only [not_exists, not_and] at h1,
  suffices : ∀ N, ∃ n, ∃ H : N ≤ n, ∀ m, N ≤ m → f m ≤ f n,
  { choose g hg1 hg2 using this,
    refine ⟨λ n, nat.rec_on n (g 0) (λ n ih, g (ih + 1)), _, _⟩,
    { apply strictly_increasing_of_nat, intros n, exact hg1 _ },
    right, apply decreasing_of_nat, intros n,
    change f (g (nat.rec _ _ n + 1)) ≤ f (nat.rec _ _ n),
    cases n with n, { apply hg2, exact nat.zero_le _ },
    apply hg2, exact le_trans (nat.le_succ_of_le $ hg1 _) (hg1 _) },
  intros N,
  suffices : ∃ n, ∀ m, f (N + m) ≤ f (N + n),
  { cases this with n hn, exact ⟨N + n, nat.le_add_right _ _, λ m hm, nat.add_sub_of_le hm ▸ hn _⟩ },
  by_contra h2, simp only [not_exists, not_forall, not_le] at h2,
  suffices : ∀ n, ∃ m, ∃ H : n < m, f (N + n) < f (N + m),
  { choose g hg1 hg2 using this,
    refine h1 (λ n, N + nat.rec_on n (g 0) (λ n ih, g ih)) _ _,
    { apply strictly_increasing_of_nat, intros n, exact add_lt_add_left (hg1 _) _ },
    apply strictly_increasing_of_nat, intros n, exact hg2 _ },
  intros n, by_contra h3, simp only [not_exists, not_lt] at h3,
  have : f 0 ∈ (finset.range $ n + 1).image f := finset.mem_image_of_mem _ (finset.mem_range.2 n.succ_pos),
  cases finset.max_of_mem this with fm hfm,
  rcases finset.mem_image.1 (finset.mem_of_max hfm) with ⟨m, hm, rfl⟩,
  rw finset.mem_range at hm,
  cases h2 m with s hs,
  sorry
end
