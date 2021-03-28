import pca
import re

namespace pca

universe variable u
variables {α : Type u}
variables [pca α]

namespace reducibility

def m_reducible (f g : α) : Prop := ∃ e : α, e ∈ (ℛ₀ : set α) ∧ (∀ x, ↓e * ↓g * ↓x = ↓f * ↓x) 
def i_reducible (f g : α) : Prop :=
  ∃ e : α, e ∈ (ℛ₀ : set α) ∧ (∀ x, ↓e * ↓g * ↓x = ↓f * ↓x) ∧ (∀ x y, ↓e * ↓x = ↓e * ↓y → x = y)
infix ` ≤ₘ `:80 := m_reducible
infix ` ≡ₘ `:80 := λ f g, f ≤ₘ g ∧ g ≤ₘ f
infix ` ≤₁ `:80 := i_reducible
infix ` ≡₁ `:80 := λ f g, f ≤₁ g ∧ g ≤₁ f
def T_reducible (f g : α) : Prop := ∃ e : α, e ∈ (ℰ₀ : set α) ∧ ↓e * ↓g = ↓f
infix ` ≤ₜ `:80 := T_reducible
infix ` <ₜ `:80 := λ f g, f ≤ₜ g ∧ ¬g ≤ₜ f
infix ` ≡ₜ `:80 := λ f g, f ≤ₜ g ∧ g ≤ₜ f

@[refl] lemma T_reducible.refl (a : α) : a ≤ₜ a :=
by { use i, split, exact prec.i, simp, }

@[trans] lemma T_reducible.trans (a b c : α) (hab : a ≤ₜ b) (hbc : b ≤ₜ c) : a ≤ₜ c :=
begin
  rcases hab with ⟨e_ab, ⟨e_ab_pr, heab⟩⟩,
  rcases hbc with ⟨e_bc, ⟨e_bc_pr, hebc⟩⟩,
  let e_ac := (0 →∅ &e_ab_pr * (&e_bc_pr * #0)),
  use e_ac,
  split,
  { show e_ac ∈ ℰ₀, simp, },
  { show ↓e_ac * ↓c = ↓a, simp [lam, expr, heab, hebc], },
end

end reducibility

end pca