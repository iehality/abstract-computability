import data.option.basic
import tactic

universe variable u
variables {α : Type u}

class partial_magma (α : Type u) :=
(mul : α → α → option α)
infixl ` ⬝ ` := partial_magma.mul
infix ` ↓= `:50 := λ x y, x = some y
prefix `↓`:80 := some

abbreviation defined : option α → bool := option.is_some

def partial_magma.mmul [partial_magma α] : option α → option α → option α
| ↓x ↓y := x ⬝ y
| _ _   := none
instance pm_mul [partial_magma α] : has_mul (option α) := {mul := @partial_magma.mmul α _}

@[simp] lemma partial_magma.none_l [partial_magma α] (p : option α) : none * p = none := option.cases_on p rfl (λ a, rfl)
@[simp] lemma partial_magma.none_r [partial_magma α] (p : option α) : p * none = none := option.cases_on p rfl (λ a, rfl)

lemma defined_l [partial_magma α] (p q : option α) : defined (p * q) → defined p :=
begin
  contrapose,
  assume (h0 : ¬ defined p),
  have e : p = none, from option.not_is_some_iff_eq_none.mp h0, 
  rw e,
  simp,
end

lemma defined_r [partial_magma α] (p q : option α) : defined (p * q) → defined q :=
begin
  contrapose,
  assume (h0 : ¬ defined q),
  have e : q = none, from option.not_is_some_iff_eq_none.mp h0, 
  rw e,
  simp,
end

abbreviation tot [partial_magma α] (a : α) : Prop := ∀ x : α, defined (a ⬝ x) = tt

/- Partial Combinatory Algebra -/
class pca (α : Type u) extends partial_magma α :=
(k : α)
(ktot : ∀ x, defined (k ⬝ x))
(k_constant : ∀ x y : α, k ⬝ x * y = x)
(s : α)
(stot : ∀ x y : α, defined (s ⬝ x * y))
(s_substitution : ∀ x y z : α, s ⬝ x * y * z = (x ⬝ z) * (y ⬝ z))

def pca.equiv [partial_magma α] (a b : option α) : Prop := ∀ x : α, a * ↓x = b * ↓x
infix ` ≃ `:50 := pca.equiv 

namespace pca

def const [pca α] (x : α) : α := option.get (ktot x)
def subst [pca α] (x y : α) : α := option.get (stot x y)
notation `𝐤` := const
notation `𝐬` := subst

@[simp] lemma k_simp [pca α] (a : α) : ↓k * ↓a = ↓(𝐤 a) := by { unfold const, simp, refl }
@[simp] lemma s_simp [pca α] (a b : α) : ↓s * ↓a * ↓b = ↓(𝐬 a b) := by { unfold subst, simp, refl }
@[simp] lemma k_simp0 [pca α] (a b : α) : ↓(𝐤 a) * ↓b = ↓a := by { rw ← k_simp, exact k_constant _ _, }
@[simp] lemma s_simp0 [pca α] (a b c : α) : ↓(𝐬 a b) * ↓c = (↓a * ↓c) * (↓b * ↓c) := by { rw ← s_simp, exact s_substitution _ _ _, }

def i [pca α] : α := 𝐬 k k
@[simp] lemma i_ident [pca α] (a : α) : ↓i * ↓a = ↓a := by { unfold i, simp, }

lemma stot0 [pca α] (a : α) : defined (↓s * ↓a) := defined_l (↓s * ↓a) a (stot _ _)

def subst0 [pca α] (x : α) : α := option.get (stot0 x)
notation `𝐬₀` := subst0

inductive lambda (α : Type u) [pca α]
| var : ℕ → lambda
| com : α → lambda
| app : lambda → lambda → lambda
instance lambda_mul (α : Type u) [pca α] : has_mul (lambda α) := ⟨lambda.app⟩

open lambda

def lam [pca α] (n : ℕ) :lambda α → lambda α
| (var m) := if n = m then com i else com k * var m
| (com c) := com k * com c
| (l * k) := (com s) * (lam l) * (lam k)
notation `Λ`x`,` := lam x 

def expr [pca α] : lambda α → option α
| (var x) := ↓k
| (com c) := ↓c
| (l * k) := (expr l) * (expr k)

lemma lambda_defined [c : pca α] : ∀ (n : ℕ) (e : lambda α), defined (expr (Λ n, e) : option α)
| n (var e) := begin
    cases (eq.decidable n e),
    { simp[lam, expr, if_neg h], exact rfl, },
    { simp[lam, expr, if_pos h], exact rfl, },
  end
| n (com c) := ktot c
| n (l * m) := begin
    simp [lam, expr], 
    let a := option.get (lambda_defined n l),
    let b := option.get (lambda_defined n m),
    have ha : expr (Λ n, l) = ↓a, { simp },
    have hb : expr (Λ n, m) = ↓b, { simp },
    rw [ha, hb],
    exact stot a b
  end

notation n` ↦ `l := option.get (lambda_defined n l)

namespace recursion

def d [pca α] : α := 0 ↦ Λ 1, (var 0 * var 0 * var 1)

lemma dtot [pca α] (f : α) : defined (d ⬝ f) :=
begin
  have e : d ⬝ f = expr (Λ 0, (com f * com f * var 0)),
  { change (d ⬝ f) with (↓d * ↓f), unfold d, simp [lam, expr], },
  rw e,
  exact (lambda_defined 0 _),
end

lemma diagonal [pca α] (f x : α) : d ⬝ f * x = f ⬝ f * x :=
begin
  calc
    d ⬝ f * ↓x = ↓d * ↓f * ↓x : rfl
    ...        = f ⬝ f * ↓x   : by { unfold d, simp [lam, expr], refl, }
end

def v [pca α] : α := 0 ↦ Λ 1, (var 0 * (com d * var 1))
def n [pca α] : α := 0 ↦ com d * (com v * var 0)

theorem recursion [pca α] (f : α) : n ⬝ f ≃ f * (n ⬝ f) :=
begin
  intros x,
  let vf := (0 ↦ com f * (com d * var 0)),  
  have hv : ↓v * ↓f = ↓vf, { unfold v, simp [lam, expr], },
  have nf_dvf : ↓n * ↓f = ↓d * ↓vf,  { unfold n, unfold v, simp [lam, expr], },
  calc
    n ⬝ f * x = ↓n * ↓f * x         : rfl
    ...       = ↓d * ↓vf * x        : by { rw nf_dvf, }
    ...       = ↓vf * ↓vf * x       : diagonal vf x
    ...       = ↓f * (↓d * ↓vf) * x : by { simp [lam, expr], }
    ...       = ↓f * (↓n * ↓f) * x  : by { rw nf_dvf, }
end

theorem ntot [pca α] (f : α) : defined (↓n * ↓f) :=
begin
  let vf := (0 ↦ com f * (com d * var 0)),  
  have hv : ↓v * ↓f = ↓vf, { unfold v, simp [lam, expr], },
  have nf_dvf : ↓n * ↓f = ↓d * ↓vf,  { unfold n, unfold v, simp [lam, expr], },
  rw nf_dvf,
  exact (dtot _)
end

end recursion

def fixpoint [pca α] : α := recursion.n
def recursion  [pca α] (f x : α) : ↓fixpoint * ↓f * ↓x = f * (↓fixpoint * ↓f) * ↓x := recursion.recursion f x
def fixpoint_of [pca α] (f : α) : α := option.get (recursion.ntot f)

namespace calculation

def pair [pca α] : α := 0 ↦ Λ 1, (Λ 2, (var 2 * var 0 * var 1))
notation `⟪`a`, `b`⟫` := 0 ↦ var 0 * com a * com b
def π₀ [pca α] : α := 0 ↦ var 0 * com k
def π₁ [pca α] : α := 0 ↦ var 0 * (com k * com i)

lemma pair_h [pca α] (a b : α) : ↓pair * ↓a * ↓b = ↓⟪a, b⟫ :=
begin
  calc
    ↓pair * ↓a * ↓b = expr (Λ 0, (Λ 1, (Λ 2, (var 2 * var 0 * var 1)))) * ↓a * ↓b
      : by { unfold pair, simp, }
    ...             = expr (Λ 0, (var 0 * com a * com b))
      : by {simp [lam, expr, if_neg (show 2 ≠ 0, from dec_trivial), if_neg (show 2 ≠ 1, from dec_trivial)], }
    ...             = ↓⟪a, b⟫
      : by { simp, },
end

lemma pair_pi0 [pca α] (a b : α) : ↓π₀ * ↓⟪a, b⟫ = ↓a := by { unfold π₀, simp [lam, expr], }
lemma pair_pi1 [pca α] (a b : α) : ↓π₁ * ↓⟪a, b⟫ = ↓b := by { unfold π₁, simp [lam, expr], }

end calculation

inductive prec [pca α] : set α
| k : prec k
| s : prec s
| mul {a b c} : ↓a * ↓b = ↓c → prec a → prec b → prec c 
notation `ℰ` := prec

def recursive [pca α] : set α := {x | prec x ∧ tot x}
notation `ℛ` := recursive
#check ℛ

lemma prec.const [pca α] {a : α} : a ∈ (ℰ : set α) → 𝐤 a ∈ (ℰ : set α) :=
begin
  assume h : a ∈ ℰ,
  have l0 : ↓k * ↓a = ↓𝐤 a, { simp, },
  show 𝐤 a ∈ ℰ, from prec.mul l0 prec.k h,
end

lemma prec.subst [pca α] {a b : α}
: a ∈ (ℰ : set α) → b ∈ (ℰ : set α) → 𝐬 a b ∈ (ℰ : set α) :=
begin
  assume (ha : a ∈ ℰ) (hb : b ∈ ℰ),
  have l0 : ↓s * ↓a = ↓𝐬₀ a, { unfold subst0, simp, },
  have l1 : 𝐬₀ a ∈ (ℰ : set α), from prec.mul l0 prec.s ha,
  have l2 : ↓𝐬₀ a * ↓b = ↓𝐬 a b, { unfold subst0, simp, },
  show 𝐬 a b ∈ ℰ, from prec.mul l2 l1 hb,
end

lemma prec.i [pca α] : i ∈ (ℰ : set α) := prec.subst prec.k prec.k

def K [pca α] : set α := {x : α | defined (↓x * ↓x)}
def re_set [pca α] (A : set α) : Prop := ∃ e : α, e ∈ (ℰ : set α) ∧ A = {x | defined (↓e * ↓x)}

lemma neg_p_iff_negp (P : Prop) : ¬(P ↔ ¬P) := 
begin
  rintros ⟨h₀, h₁⟩,
  have h₂ : ¬ P := λ p, h₀ p p,
  exact h₂ (h₁ h₂),
end

lemma K_re [pca α] : re_set (K : set α) :=
begin
  use (0 ↦ var 0 * var 0),
  have h : ∀ x : α, expr (Λ 0, (var 0 * var 0)) * ↓x = ↓x * ↓x, { intros x, simp [lam, expr], },
  split,
  { simp [lam, expr],
    show 𝐬 i i ∈ ℰ, from prec.subst prec.i prec.i, },
  apply set.ext,
  intros x,
  split,
  { assume xK, simp, rw h x, exact xK, },
  { unfold K, simp, assume xh, rw ← h x, exact xh, },
end

lemma compl_K_nre [pca α] : ¬ re_set (Kᶜ : set α) :=
begin
  rintro ⟨e, h⟩,
  apply neg_p_iff_negp (e ∈ (K : set α)),
  split,
  { assume eK : e ∈ K,
    show e ∈ (Kᶜ : set α), { rw h.2, simp, exact eK, }, },
  { assume nKc : e ∉ K,
    have eKc : e ∈ (Kᶜ : set α) := nKc,
    show e ∈ K, { unfold K, simp, rw h.2 at eKc, exact eKc, }, },
end


end pca
