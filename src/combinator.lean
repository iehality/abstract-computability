import pca
import re

namespace pca

universe variable u
variables {α : Type u}
variables [pca α]

def pair : α := 0 →∅ Λ 1, (Λ 2, (#2 * #0 * #1))
notation `⟪`a`, `b`⟫` := 𝚜 (𝚜 i (𝚔 a)) (𝚔 b)
def π₀ : α := 0 →∅ #0 * &submodel.k
def π₁ : α := 0 →∅ #0 * (&submodel.k * &submodel.i)

@[simp] lemma pair_e [pca α] (a b : α) : ↓pair * ↓a * ↓b = ↓⟪a, b⟫ :=
by simp [pair, lam, expr, if_neg (show 2 ≠ 0, from dec_trivial), if_neg (show 2 ≠ 1, from dec_trivial)]

@[simp] lemma pair_pi0 [pca α] (a b : α) : ↓π₀ * ↓⟪a, b⟫ = ↓a := by simp [π₀, lam, expr]
@[simp] lemma pair_pi1 [pca α] (a b : α) : ↓π₁ * ↓⟪a, b⟫ = ↓b := by simp [π₁, lam, expr]

def top [pca α] : α := 0 →∅ Λ 1, #0
def bot [pca α] : α := 0 →∅ Λ 1, #1

notation `𝚃` := top
notation `𝙵` := bot


end pca