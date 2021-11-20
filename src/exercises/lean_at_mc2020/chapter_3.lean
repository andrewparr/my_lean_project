-- 3. Infinitely Many Primes

-- Today we will prove that there are infinitely many primes using mathlib library.
-- Our focus will be on how to use the library to prove more complicated theorems. 

-- 3.1. Equality

import tactic data.nat.basic
open nat
open function

/--------------------------------------------------------------------------

  ``rw``

    If ``f`` is a term of type ``P = Q`` (or ``P ↔ Q``), then
    ``rw f`` replaces ``P`` with ``Q`` in the target.
    Other variants:
      ``rw f at hp``, ``rw ←f``, ``rw ←f at hr``.

  Delete the ``sorry,`` below and replace them with a legitimate proof.

  --------------------------------------------------------------------------/

theorem add_self_self_eq_double(x : ℕ) : x + x = 2 * x :=
begin
  ring,
end

/-
For the following problem, use
  mul_comm a b : a * b = b * a
-/

example (a b c d : ℕ)
  (hyp : c = d * a + b)
  (hyp' : b = a * d)
: c = 2 * (a * d) :=
begin
  rw hyp,
  rw hyp',
  ring,   
end

-- The above was solved, but comment above says to use mul_comm, so here's another go
example (a b c d : ℕ)
  (hyp : c = d * a + b)
  (hyp' : b = a * d)
: c = 2 * (a * d) :=
begin
  -- In order to use mul_comm I had to eliminate the 2 * first by using two_mul
  rw two_mul,
  rw hyp,
  rw hyp',
  rw mul_comm, -- then can use mul_comm with tries refl afterwards and this solves the goal.
end

/-
For the following problem, use
  sub_self (x : ℕ) : x - x = 0
-/

example (a b c d : ℕ)
  (hyp : c = b * a - d)
  (hyp' : d = a * b)
: c = 0 :=
begin
  rw hyp,
  rw hyp',
  -- goal is now b * a - a * b, so we can't yet apply rw sub_self
  rw mul_comm, -- now have a * b - a * b, but 
  -- rw ← hyp', -- this replaces both sets of a * b to d
  -- rw nat.sub_self d,
  rw nat.sub_self _, -- you don't actually need to reduce the a * b to d
  -- I'm not sure why I needed nat.sub_self. But just using rw sub_self didn't work. 
end

-- 3.1.1. Surjective functions

--  Recall that a function f : X → Y is surjective if for every y : Y there exists a term x : X such that
--  f(x) = y. In type theory, for every function f we can define a corresponding proposition
--  surjective (f) := ∀ y, ∃ x, f x = y and a function being surjective is equivalent to saying
--  that the proposition surjective(f) is inhabited.

/--------------------------------------------------------------------------

``unfold``

  If it gets hard to keep track of the definition of ``surjective``,
  you can use ``unfold surjective,`` or ``unfold surjective at h,``
  to get rid of it.

Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

variables X Y Z : Type
variables (f : X → Y) (g : Y → Z)

/-
surjective (f : X → Y) := ∀ y, ∃ x, f x = y
-/

example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
begin
  -- These unfolds aren't necessary, bu they help to see the proof.
  unfold surjective,
  unfold surjective at hf,
  unfold surjective at hg,
  -- our goal is ∀ (b : Z) .., so we can introduce an arbitary z.
  intro z,
  -- we can now use hg with this z, to give use a y : Y
  -- we do this be creating the hypothesis that there must exist a y : Y
  have h1 : ∃ y : Y, g y = z, from hg z,
  -- and then uses cases on this hypothesis to obtain an arbitary y : Y
  cases h1 with y,
  -- similar as above, we now use hf with this y to first creat the hypothesis
  -- that an x : X must exist
  have h2 : ∃ x : X, f x = y, from hf y,
  -- then use cases to obtiain an arbitary x : X
  cases h2 with x,
  -- finally our goal is in sight, the goal is to prove
  -- ∃ (a : X), (g ∘ f) a = z
  -- and we can just use the x : X that we have proved exists above.
  use x,
  -- the finish tatic will now finish this proof.
  finish,
  -- If you use suggest rather than finish above, it suggest the following to finish the proof.
  -- exact (eq.congr_right h1_h).mp (congr_arg g (eq.symm h2_h)).symm,
 end

example
  (hgf : surjective (g ∘ f))
  : surjective g :=
begin
  unfold surjective,
  unfold surjective at hgf,
  intro z,
  have h1 : ∃ (a : X), (g ∘ f) a = z, from hgf z,
  cases h1 with x h2,
  
  --have y : Y, from f x,
  have hh : ∃ (y : Y), y = f x :=
  begin
    use f x,
  end,
  cases hh with y,

  use y,
  
  

  --induction h2,  
  --have y : Y, from f x,
  --use y,
  --have hh : y = f x := begin
  --  induction h2,
  --end,
  --use y,
  
  --have hh : f x - (y : Y), from f x, -- where is proof that y = f x
  -- WHat is my proof here ?
  sorry,
end

/--

Proof, take any z ∈ Z,
since g ∘ f is surjective, ∃ x ∈ X, s.t. (g ∘ f) x = z,
so g(f(x)) = z,
set y = f(x) , note y ∈ Y.
then, g(b) = g(f(x)) = y
see https://www.youtube.com/watch?v=bTKOC3Rst8c

--/