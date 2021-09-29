-- The rintro tactic is a combination of the intros tactic with rcases
-- to allow for destructuring patterns while introducing variables

-- See https://leanprover-community.github.io/mathlib_docs/tactics.html#rintro

import tactic

variables (P Q R : Prop)

-- For example, Here we prove with first intro and then cases.
example : P ∧ Q → Q ∧ P :=
begin
  intro h,
  cases h with hP hQ,
  split; assumption
end

-- Using rintro, we can combine the intro and cases on to one line
example : P ∧ Q → Q ∧ P :=
begin
  rintro ⟨hP, hQ⟩,
  split; assumption
end

-- In term mode, this can be written using λ
example : P ∧ Q → Q ∧ P :=
λ⟨hP, hQ⟩, ⟨hQ, hP⟩

-- Note the ⟨ ⟩ in the rintro can be nested
example : ((P ∧ Q) ∧ R) → (P ∧ Q ∧ R) :=
begin
  rintro ⟨⟨hP, hQ⟩, hR⟩,
  exact ⟨hP, hQ, hR⟩,
end

-- and this in term mode becomes
example : ((P ∧ Q) ∧ R) → (P ∧ Q ∧ R) :=
λ ⟨⟨hP, hQ⟩, hR⟩, ⟨hP, hQ, hR⟩

-- Note, when the cases causes two goals.
example : P ∨ Q  → Q ∨ P :=
begin
  intro h,
  cases h with hP hQ,
  -- here we now have two goals
  {
    -- goal is given hP : P, prove Q ∨ P
    right, exact hP
  },
  {
    -- here goal is given hQ : Q, prove P ∨ R
    left, exact hQ
  }
end

-- In this case you need to use ( | ) notation with rcases
example : P ∨ Q  → Q ∨ P :=
begin
  rintro (hP | hQ),
    right, exact hP,
  left, exact hQ
end

-- In term mode, this uses the definition of or as an inductive type
-- and constructs the required proof directly from the parts.
example : P ∨ Q  → Q ∨ P :=
  or.rec or.inr or.inl
