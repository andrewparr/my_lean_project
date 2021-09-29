import tactic

variables P Q : Prop

example (hP : P) : P ∨ Q :=
begin
  left,
  assumption,
end

example (hQ : Q) : P ∨ Q :=
begin
  right,
  assumption,
end

example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split;
  assumption,
end

