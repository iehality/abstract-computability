import pca

namespace pca

universe variable u
variables {α : Type u}

namespace combinator

def pair [pca α] : α := 0 ↦ Λ 1, (Λ 2, (#2 * #0 * #1))
notation `⟪`a`, `b`⟫` := 0 ↦ #0 * (&a) * &b
def π₀ [pca α] : α := 0 ↦ #0 * &k
def π₁ [pca α] : α := 0 ↦ #0 * (&k * &i)

lemma pair_h [pca α] (a b : α) : ↓pair * ↓a * ↓b = ↓⟪a, b⟫ :=
begin
  calc
    ↓pair * ↓a * ↓b = expr (Λ 0, (Λ 1, (Λ 2, (#2 * #0 * #1)))) * ↓a * ↓b
      : by { unfold pair, simp, }
    ...             = expr (Λ 0, (#0 * &a * &b))
      : by {simp [lam, pca.expr, if_neg (show 2 ≠ 0, from dec_trivial), if_neg (show 2 ≠ 1, from dec_trivial)], }
    ...             = ↓⟪a, b⟫
      : by { simp, },
end

lemma pair_pi0 [pca α] (a b : α) : ↓π₀ * ↓⟪a, b⟫ = ↓a := by { unfold π₀, simp [lam, pca.expr], }
lemma pair_pi1 [pca α] (a b : α) : ↓π₁ * ↓⟪a, b⟫ = ↓b := by { unfold π₁, simp [lam, pca.expr], }

def top [pca α] : α := 0 ↦ Λ 1, (#0)
def bot [pca α] : α := 0 ↦ Λ 1, (#1)

end combinator
end pca