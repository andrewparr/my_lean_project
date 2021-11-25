import tactic

/-
When writing proofs it's easier to write them in tactic mode.
The show_term command will show you the term mode proof for this tactic proof.
If the term mode proof is shorter, this is how the proof would be written in mathlib.
-/

-- Let P and Q be propositions.
variables P Q : Prop

-- The following is a simple proof that if we have P ∧ Q, then we also have Q ∧ P
example : P ∧ Q → Q ∧ P :=
begin
  intro h,
  split,
  exact h.right,
  exact h.left,
end

-- to write this in term_mode, use the show_term command like this

example : P ∧ Q → Q ∧ P :=
begin
  show_term {
    intro h,
    split,
    exact h.right,
    exact h.left,
  },
end

-- Clicking the show_term word above and then clicking the try this command in the infoview window will reduce this to

example : P ∧ Q → Q ∧ P :=
begin
  exact λ (h : P ∧ Q), ⟨h.right, h.left⟩,
end

-- Finally we can remove the begin exact and end parts to reduce this to
example : P ∧ Q → Q ∧ P := λ (h : P ∧ Q), ⟨h.right, h.left⟩

