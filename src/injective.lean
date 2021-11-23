variables (X Y Z : Type) (f : X → Y) (g : Y → Z)

open function

example (hf : injective f) (hg : injective g) : injective (g ∘ f) :=
begin
  intros x₁ x₂ h,
  apply hf,
  apply hg,
  exact h,
end
