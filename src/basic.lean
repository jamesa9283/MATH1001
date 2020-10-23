import data.real.basic
-- we need to know that the reals are a thing.


/- Let us define some bits about the complex numbers! We shall also use this as an 
    oppourtunity to understand what happens when we define a new 'set' of numbers in Lean.
    To define a new set of numbers we need to do some things, these things may be seen as very
    simple or even obvious to us, but we have to remember that Lean doesn't understand anything
    we don't tell it. At the moment it knows nothing about Complex Numbers, it only knows things
    about the reals. -/


/- Firstly we start with what we call a `structure`, this is a way to denote how the number 
    shall be written. We let the structure be a type, meaning it is a 'set', by writing:
    `structure complex : Type`. Then we tell Lean how we want the structure of our thing to 
    look, in this case we want two real numbers. So we write: `(re: ℝ) (im: ℝ)`, which says as
    we said above, two reals. We call the first `re`, our real part and second, `im`, our 
    imaginary part. This corresponds with how we write complex numbers in a more normal way: 
    `a + bi`   

    NB! To write ℝ in lean, just use \R and press your space bar
-/
structure complex : Type :=
(re : ℝ) (im : ℝ)

/- As Lean knows nothing about the complex numbers, we have to tell it how to denote the set,
    So here we are telling Lean that we notate the set of complexes with ℂ, please carefully 
    note that there are backticks around the ℂ, I spent too long trying to work out why my 
    notation code wasn't working when I first started Lean. We shall also note that `:=` means
    is defined as. 
-/
notation `ℂ` := complex

/- Let us take an example of a complex number, `3 + 4i`, we can write this rather easily in
    a multide of ways.
-/
example : ℂ :=
{ re := 3,
  im := 4 }

-- Or like this:
example : ℂ := complex.mk 3 4

-- or like this:
example : ℂ := ⟨3, 4⟩

-- They all give the same complex number.

namespace complex -- This tells us that what we are doing from here on in is in is about the
                  -- complexes.


/-! # Zero -/

/- Now we need to define what a zero is in this new and rather strange number system, this
    may look a bit odd at first, but I shall talk / walk you through whats going on here -/

-- This says, let us define a zero in the complexes and we define it as the diple `⟨0, 0⟩`, 
-- or if you prefer, `complex.mk 0 0`. 
def zero : ℂ := ⟨0, 0⟩

-- Now we set up notation so that `0 : ℂ` will mean `zero`. 

/- This does something very similar to before and instead of using the command `notation`, 
    we define a zero using `has_zero`, which is a typeclass. Basically what this does is it 
    allows us to use the `(0 : ℂ)`, which says `0` is a complex.  -/
instance : has_zero ℂ := ⟨zero⟩

/- If I give you the famed `(0 : ℂ)` from the line above, now I ask you to prove that 
    following, that the real part of `0` is zero and the complex part of `0` is zero. Obviously
    these are true by definition, or reflexivly true. So we can write `rfl` as the proof, the
    shortened term mode brother of refl. -/

@[simp] lemma zero_re : re(0 : ℂ) = 0 := rfl
@[simp] lemma zero_im : im(0 : ℂ) = 0 := rfl

/- Now for a few exercises or even examples: -/

--C01
example : re( ⟨1, 2⟩ ) = 1 := 
begin
  sorry
end

--C02
example (a b : ℝ) : im( ⟨a + b, b⟩ ) = b :=
begin
  sorry
end

--*C03
/-- For the following example, you will need to `rw` instead the `refl` that you need is 
    `add_comm`. Note that Lean does a refl after every `rw` -/
example (a b : ℝ) : re( ⟨a + b, b⟩ ) = b + a :=
begin
  sorry
end

/- # One -/
/- As you probably guessed we needed the zero as a additive identity, so now we need a 
    multiplicative identity. We are going to do basically the same thing as we did for zero, 
    so less annoying comments this time! -/

/-- The complex number with real part 1 and imaginary part 0 -/
def one : ℂ := ⟨1, 0⟩

/-- Notation `1` for `one` -/
instance : has_one ℂ := ⟨one⟩ 

-- name the basic properties and tag them with `simp`
@[simp] lemma one_re : re(1 : ℂ) = 1 := begin refl end
@[simp] lemma one_im : im(1 : ℂ) = 0 := begin refl end

/- Before I give you some more examples or exercises let's just quickly define the operations. It 
    again works in a very similar way to before when we defined `0` and `1`. -/

/- # Add (+) -/

/- This says take two numbers: `z = a  bi` and `w = u + vi` and then when we add them, just 
    add their real parts and then add their imaginary parts and define 
    `z + w = (a + u) + (b + v)i` -/
def add (z w : ℂ) : ℂ := ⟨z.re + w.re, z.im + w.im⟩

/-- Notation `+` for addition -/
instance : has_add ℂ := ⟨add⟩

/-- Let us define some more bits that is similar, to above -/
@[simp] lemma add_re (z w : ℂ) : re(z + w) = re(z) + re(w) := begin refl end
@[simp] lemma add_im (z w : ℂ) : im(z + w) = im(z) + im(w) := begin refl end

/- # Negation (-) -/
-- We note as mathematicians, that `a - b = a + -b` and so if we define negation, we then
-- don't have to define subtraction.

/-- The negation `-z` of a complex number `z` -/
def neg (z : ℂ) : ℂ := ⟨-re(z), -im(z)⟩

/-- Notation `-` for negation -/
instance : has_neg ℂ := ⟨neg⟩

-- how neg interacts with re and im
@[simp] lemma neg_re (z : ℂ) : re(-z) = -re(z) := begin refl end
@[simp] lemma neg_im (z : ℂ) : im(-z) = -im(z) := begin refl end

/- ## Multiplication (*) -/

/-- Multiplication `z*w` of two complex numbers -/
def mul (z w : ℂ) : ℂ := ⟨re(z) * re(w) - im(z) * im(w), re(z) * im(w) + im(z) * re(w)⟩

/-- Notation `*` for multiplication -/
instance : has_mul ℂ := ⟨mul⟩

-- how `mul` reacts with `re` and `im`
@[simp] lemma mul_re (z w : ℂ) : re(z * w) = re(z) * re(w) - im(z) * im(w) := begin refl end
@[simp] lemma mul_im (z w : ℂ) : im(z * w) = re(z) * im(w) + im(z) * re(w) := begin refl end






end complex