import ext_comm_ring

open complex

/-- # Examples -/

/-- We will need to learn a completely new tactic, we can use the `ext` tactic to show that
    if two complex numbers have the same real and imaginary parts, then they are the same.
    The astute eyed among you, will notice that there is a semi-colon after the `ext`, this
    applies the tactic before it to any new goals created by the tactic. -/
example : (⟨1, 2⟩ : ℂ) + ⟨2, 3⟩  = ⟨3, 5⟩ :=
begin
  ext;
  norm_num,
end
/- `norm_num` is Lean's way of dealing with arithmentic -/

--C04
example (a b c : ℝ) : (⟨a, b⟩ : ℂ) + ⟨b, c⟩ = ⟨ a + b, b + c⟩ := 
begin 
  sorry
end

/- Do this twice, once with `zero_add` -/
--C05a
example (α : ℂ) : (0 : ℂ) + α = α :=
begin
  sorry
end 

-- C05b
example (α : ℂ) : (0 : ℂ) + α = α :=
begin
  sorry
end

/- Theres a useful command called `ring` -/
-- C07
example (a b c d : ℝ): (⟨a, b⟩ : ℂ) * (⟨c, d⟩ : ℂ) = (⟨ a*c - b*d, a*d + b*c⟩ : ℂ) :=
begin
  ext;
  ring,
end

lemma complex.add_assoc (a b c : ℂ) : a + b + c = a + (b + c) :=
begin
  intros,
  ext;
  simp [add_re];
  ring,
end



/-- The complex numbers are a commutative ring -/
instance : comm_ring ℂ :=
begin
  -- first the data
  refine_struct {
      zero := (0 : ℂ), add := (+), neg := has_neg.neg, one := 1, mul := (*),
  ..},
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
  sorry,
end
