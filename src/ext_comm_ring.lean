import tactic basic

namespace complex

/-! # `ext` : A mathematical triviality -/

/- 
Two complex numbers with the same and imaginary parts are equal.
This is an "extensionality lemma", i.e. a lemma of the form "if two things
are made from the same pieces, they are equal".
This is not hard to prove, but we want to give the result a name
so we can tag it with the `ext` attribute, meaning that the
`ext` tactic will know it. To add to the confusion, let's call the theorem `ext` :-)
-/

/-- If two complex numbers z and w have equal real and imaginary parts, they are equal -/
@[ext] theorem ext {z w : ℂ} (hre : re(z) = re(w)) (him : im(z) = im(w)) : z = w :=
begin
  cases z with zr zi,
  cases w with ww wi,
  simp at *,
  /- goal now a logic puzzle
  
  hre : zr = ww,
  him : zi = wi
  ⊢ zr = ww ∧ zi = wi
  
  -/
  cc,
end

/-! # Theorem:  The complex numbers are a commutative ring -/

-- Proof: we've defined all the structure, and every axiom can be checked by reducing it
-- to checking real and imaginary parts with `ext`, expanding everything out with `simp`
-- and then using the fact that the real numbers are a commutative ring.
instance : comm_ring ℂ :=
begin
  -- first the data
  refine_struct {
      zero := (0 : ℂ), add := (+), neg := has_neg.neg, one := 1, mul := (*),
  ..},
  -- now the axioms
  -- of which there seem to be 11
  -- introduce the variables
  all_goals {intros},
  -- we now have to prove an equality between two complex numbers.
  -- It suffices to check on real and imaginary parts
  all_goals {ext},
  -- the simplifier can simplify stuff like re(a+0)
  all_goals {simp},
  -- all the goals now are identities between *real* numbers,
  -- and the reals are already known to be a ring
  all_goals {ring},
end


-- That is the end of the proof that the complexes form a ring. We built
-- a basic API which was honed towards the general idea that to prove
-- certain statements about the complex numbers, for example distributivity,
-- we could just check on real and imaginary parts. We trained the
-- simplifier to expand out things like re(z*w) in terms
-- of re(z), im(z), re(w), im(w).

/-!

# Optional section for mathematicians : more basic infrastructure, and term mode

-/

/-! 
## `ext` revisited

Recall extensionality:

`theorem ext {z w : ℂ} (hre : re(z) = re(w)) (him : im(z) = im(w)) : z = w := ...`

Here is another tactic mode proof of extensionality. Note that we have moved
the hypotheses to the other side of the colon; this does not
change the theorem. This proof shows the power
of the `rintros` tactic.
-/

theorem ext' : ∀ z w : ℂ, z.re = w.re → z.im = w.im → z = w :=
begin
  rintros ⟨zr, zi⟩ ⟨_, _⟩ ⟨rfl⟩ ⟨rfl⟩,
  refl,
end


/-
Explanation: `rintros` does `cases` as many times as you like using this cool `⟨ ⟩` syntax
for the case splits. Note that if you say that a proof of `a = b` is `rfl` then
Lean will define a to be b, or b to be a, and not even introduce new notation for it.
-/

-- Here is the same proof in term mode.

theorem ext'' : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
| ⟨zr, zi⟩ ⟨_, _⟩ rfl rfl := rfl

/-!
## `eta`
-/

/-
We prove the mathematically obvious statement that the
complex number whose real part is re(z) and whose imaginary
part is im(z) is of course equal to z.
-/

/-- ⟨z.re, z.im⟩ is equal to z -/
@[simp] theorem eta : ∀ z : ℂ, complex.mk z.re z.im = z :=
begin
  intro z,
  cases z with x y, 
  /-
    goal now looks complicated, and contains terms which look
    like {re := a, im := b}.re which obviously simplify to a.
    The `dsimp` tactic will do some tidying up for us, although
    it is not logically necessary. `dsimp` does definitional simplification.
  -/
  dsimp,
  -- Now we see the goal can be solved by reflexivity
  refl,
end

/-
The proof was "unfold everything, and it's true by definition".
This proof does not teach a mathematician anything, so we may as well write
it in term mode. Many tactics have term mode equivalent.
The equation compiler does the `intro` and `cases` steps,
and `dsimp` was unnecessary -- the two sides of the equation 
were definitionally equal.
-/

theorem eta' : ∀ z : ℂ, complex.mk z.re z.im = z
| ⟨x, y⟩ := rfl

/-!
## ext_iff
-/

/-
Note that `ext` is an implication -- if re(z)=re(w) and im(z)=im(w) then z=w.
The below variant `ext_iff` is the two-way implication: two complex
numbers are equal if and only if they have the same real and imaginary part.
Let's first see a tactic mode proof. See how the `ext` tactic is used?
After it is applied, we have two goals, both of which are hypotheses.
The semicolon means "apply the next tactic to all the goals produced by this one"
-/

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
begin
  split,
  { intro H,
    simp [H]},
  {
    rintro ⟨hre, him⟩,
    ext; assumption,
  }
end

-- Again this is easy to write in term mode, and no mathematician
-- wants to read the proof anyway.

theorem ext_iff' {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
⟨λ H, by simp [H], and.rec ext⟩

end complex

/-!

# some last comments on the `simp` tactic

Some equalities, even if obvious, had to be given names, because we want `simp`
to be able to use them. In short, the `simp` tactic tries to solve
goals of the form A = B, when `refl` doesn't work (i.e. the goals are
not definitionally equal) but when any mathematician would be able
to simplify A and B via "obvious" steps such as `0 + x = x` or
`⟨z.re, z.im⟩ = z`. These things are sometimes not true by definition,
but they should be tagged as being well-known ways to simplify an equality.
When building our API for the complex numbers, if we prove a theorem of the
form `A = B` where `B` is a bit simpler than `A`, we should probably
tag it with the `@[simp]` attribute, so `simp` can use it.

Note: `simp` does *not* prove "all simple things". It proves *equalities*.
It proves `A = B` when, and only when, it can do it by applying 
its "simplification rules", where a simplification rule is simply a proof
of a theorem of the form `A = B` and `B` is simpler than `A`.  
-/


------------------ VERY INTERESTING BITS -------------------------

/-- The canonical map from ℝ to ℂ. -/
def of_real (r : ℝ) : ℂ := ⟨r, 0⟩ 

/-
We make this map into a *coercion*, which means that if `(r : ℝ)` is a real
number, then `(r : ℂ)` or `(↑r : ℂ)` will indicate the corresponding
complex number with no imaginary part. This is the notation we shall
use in our `simp` lemmas.
-/

/-- The coercion from ℝ to ℂ sending `r` to the complex number `⟨r, 0⟩` -/
instance : has_coe ℝ ℂ := ⟨of_real⟩