import tactic
-- the next two lines let us use the by_cases tactic without trouble
noncomputable theory
open_locale classical

-- 2.1.2. Proofs as functions

-- Every time you successfully construct a proof of a theorem say
theorem tautology (P : Prop) : P → P :=
begin
  intro hp,
  exact hp,
end

-- Lean constructs a proof term tautology : ∀ P : Prop, P → P (you can see this by typing #check tautology).
#check tautology


-- Once constructed, any term can be used in a later proof. For example,
example (P Q : Prop) : (P → Q) → (P → Q) :=
begin
  exact tautology (P → Q),
end

-- This is how Lean simulates mathematics.
-- Every time you prove a theorem using tactics a proof term gets created.
-- Because of proof irrelevance, Lean forgets the exact content of the proof and only remembers its type.
-- All the proof terms can then be used in later proofs.
-- All of this falls under the giant umbrella of the Curry–Howard correspondence.

-- 2.2 And / Or

/--------------------------------------------------------------------------

``cases``

  ``cases`` is a general tactic that breaks up complicated terms.
  If ``hpq`` is a term of type ``P ∧ Q`` or ``P ∨ Q`` or ``P ↔ Q``, then use
  ``cases hpq with hp hq,``.

``split``

  If the target of the current goal is ``P ∧ Q`` or ``P ↔ Q``, then use
  ``split,``.

``left``/``right``

  If the target of the current goal is ``P ∨ Q``, then use
  either ``left,`` or ``right,`` (choose wisely).

``exfalso``

  Changes the target of the current goal to ``false``.

Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

example (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  intro hpq,
  cases hpq with hp hq,
  split,
  exact hq,
  exact hp,
end

example (P Q : Prop) : P ∨ Q → Q ∨ P :=
begin
  intro hpq,
  cases hpq with hp hq,
  {
    right,
    exact hp,
  }, {
    left,
    exact hq,
  }
end

example (P Q R : Prop) : P ∧ false ↔ false :=
begin
  split,
  {
    -- here we need to prove P ∧ false → false
    intro hPnFalse,
    cases hPnFalse with hp hfalse,
    exact hfalse,
  },
  {
      -- here we need to prove false → P ∧ false
      intro h,
      exfalso,
      exact h,
  }
end

theorem principle_of_explosion (P Q : Prop) : P ∧ ¬ P → Q :=
begin
  intro hPnP,
  cases hPnP with hP hnP,
  exfalso,
  apply hnP,
  exact hP,
end

-- 2.3. Quantifiers

-- 2.3.1. Barber paradox

/--------------------------------------------------------------------------

``by_cases``

  If ``P`` is a proposition, then ``by_cases P,`` creates two goals,
    the first with a hypothesis ``hp: P`` and
    second with a hypothesis ``hp: ¬ P``.

Delete the ``sorry,`` below and replace them with a legitimate proof.

--------------------------------------------------------------------------/

-- men is type.
-- x : men means x is a man in the town
-- shaves x y is inhabited if x shaves y

variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

/--------------------------------------------------------------------------
The claim is that in a certain town there is a (male) barber that shaves all
the men who do not shave themselves. (Why is this a paradox?) Prove that this
is a contradiction.

I found this complicated - the outline of the proof is as follows:

Use proof by contradiction, so first assume
  shaves barber x ↔ ¬ shaves x x
I.e. we are assuming both
  p1: shaves barber x → ¬ shaves x x
and
  p2: ¬ shaves x x → shaves barber x

assume shaves barber x
then by p1, we also have ¬ shaves x x
but barber is a man and this means ¬ shaves barber x
which is a contradiction.
This contradiction means the assumption above is invalid and so ¬ assume shaves barber x

Now assuming
¬ shaves barber x
then by p2 we must have shaves barber x
this is also a contraction.

This second contraction, means the initial assumption was wrong and so
this completes the proof.
---------------------------------------------------------------------------/

example : ¬ (∀ x : men, shaves barber x ↔ ¬ shaves x x) :=
begin
  -- we prove by contradiction, so assume it's true
  by_contradiction,
  -- x is a barber
  have x := barber,
  -- h is currently (x : men), shaves barber x ↔ ¬shaves x x
  -- so lets specialize to just get
  -- h : h: shaves barber x ↔ ¬shaves x x
  specialize h x,
  -- since h is a ↔ hypothesis, we do cases on it.
  cases h with p1 p2,
  by_cases shaves barber barber,  
  { 
    -- goal here is false, and have h : shaves barber barber
    
    sorry,  
  },
  {
    -- goal here is false and have h : ¬ shaves barber barber
    sorry,
  }
end
