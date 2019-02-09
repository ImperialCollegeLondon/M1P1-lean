import data.real.basic tactic.linarith

open real

-- a non-empty bounded-above set S has a max iff sup(S) is in S
theorem Q2d (S : set ℝ) (h1 : ∃ s, s ∈ S) (h2 : ∃ B, ∀ s ∈ S, s ≤ B) :
(∃ m ∈ S, ∀ s ∈ S, s ≤ m) ↔ real.Sup S ∈ S :=
begin
  let t := Sup S,
  -- let's get the key fact about t before we start, namely that t is 
  -- a least upper bound!
  -- First let's get the variables from h1 and h2
  cases h1 with s Hs,
  cases h2 with b Hb,
  -- then let's apply the theorem we need.
  have H : is_lub S t := real.is_lub_Sup Hs Hb,
  -- Now we don't need s Hs b Hb any more
  clear Hs s Hb b,
  -- Now we know that t is the least upper bound for S.
  -- Goal still mentions Sup S -- let's change to t.
  change _ ↔ t ∈ S,
  -- Before we start, let's break down H (the statement that t is a LUB for S
  -- into its two parts -- that t is an UB and that t is ≤ all UBs)
  cases H with Ht1 Ht2, 
  -- Now let's start.
  split,
  { rintro ⟨m,Hm,Hmax⟩, -- assuming there's a max, call it m.
    -- t is the sup, m is the max. We know m ∈ S, we prove t ∈ S by showing t = m.
    convert Hm,
    have H1 : t ≤ m,
      apply Ht2,
      exact Hmax,
    have H2 : m ≤ t,
      apply Ht1,
      exact Hm,
    linarith },
  { -- sup in S implies its the max
    intro Ht,
    use t,
    use Ht,
    exact Ht1 },
end

theorem Q2f (S : set ℝ) (a : ℝ) :
is_lub S a ∧ is_glb (-S) a ↔
  S = {x : ℝ | x < a} ∨ S = {x : ℝ | x ≤ a}
:=
begin
  split,
  { rintro ⟨h1,h2⟩,
    change is_glb (-S) _ at h2,
    have h3 : ∀ x : ℝ, x < a → x ∈ S,
    { intros x Hx,
      suffices : ¬ (x ∈ -S),
        rw ←set.mem_compl_eq at this,
        rw set.compl_compl at this,
        assumption,
      intro HS,
      have := h2.1 x HS,
      linarith,
    },
    have h4 : ∀ x : ℝ, x > a → x ∈ -S,
      intros x Hx HS,
      have := h1.1 x HS,
      linarith,
    -- So everything < a is in S, and everything > a is not in S.
    -- Now split into cases depending on whether a ∈ S or not.
    cases classical.em (a ∈ S),
    { -- a ∈ S
      right,
      -- two sets are equal iff they have the same elements
      ext,
      split,
      { exact h1.1 x },
      { intro Hx,
        change x ≤ a at Hx,
        rw le_iff_lt_or_eq at Hx,
        cases Hx,
          exact h3 x Hx,
          rwa ←Hx at h
      },
    },
    { left,
      ext,split,
        intro Hx,
        show x < a,
        apply lt_of_le_of_ne,
          exact h1.1 x Hx,
        intro Hxa,
        apply h,
        convert Hx,
        rw Hxa,
      intro Hxa,
      change x < a at Hxa,
      rw ←set.compl_compl S,
      intro h5,
      have := h2.1 x h5,
      linarith }
  },
  intro HS,
  cases HS with H1 H2,
  { rw H1, clear H1, split,
    { split,
      { intros x Hx, exact le_of_lt Hx},
      { intros b Hb,
        apply le_of_not_gt,
        intro Ha,
        have Hc := Hb ((b + a) / 2) (show _ < a, by linarith),
        linarith },
    },
    { have H1 : -{x : ℝ | x < a} = {x : ℝ | a ≤ x},
        ext,simp,
      rw H1, clear H1, split,
      { intros x Hx,exact Hx },
      { intros b Hb,
        exact Hb a (le_refl _),
        sorry },
    },
  },
  {
    sorry
  }
end