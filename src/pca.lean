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

lemma defined_l [partial_magma α] {p q : option α} : defined (p * q) → defined p :=
begin
  contrapose,
  assume (h0 : ¬ defined p),
  have e : p = none, from option.not_is_some_iff_eq_none.mp h0, 
  rw e,
  simp,
end

lemma defined_r [partial_magma α] {p q : option α} : defined (p * q) → defined q :=
begin
  contrapose,
  assume (h0 : ¬ defined q),
  have e : q = none, from option.not_is_some_iff_eq_none.mp h0, 
  rw e,
  simp,
end

def tot [partial_magma α] (a : α) : Prop := ∀ x : α, defined (↓a * ↓x) = tt

/- Partial Combinatory Algebra -/
class pca (α : Type u) extends partial_magma α :=
(k : α)
(ktot : ∀ x, defined (k ⬝ x))
(k_constant : ∀ x y : α, k ⬝ x * y = x)
(s : α)
(stot' : ∀ x y : α, defined (s ⬝ x * y))
(s_substitution : ∀ x y z : α, s ⬝ x * y * z = (x ⬝ z) * (y ⬝ z))

def pca.equiv [partial_magma α] (a b : option α) : Prop := ∀ x : α, a * ↓x = b * ↓x
infix ` ≃ `:50 := pca.equiv 

namespace pca

def const [pca α] (x : α) : α := option.get (ktot x)
def subst [pca α] (x y : α) : α := option.get (stot' x y)
notation `𝐤` := const
notation `𝐬` := subst

@[simp] lemma k_simp [pca α] (a : α) : ↓k * ↓a = ↓(𝐤 a) := by { unfold const, simp, refl }
@[simp] lemma s_simp [pca α] (a b : α) : ↓s * ↓a * ↓b = ↓(𝐬 a b) := by { unfold subst, simp, refl }
@[simp] lemma k_simp0 [pca α] (a b : α) : ↓(𝐤 a) * ↓b = ↓a := by { rw ← k_simp, exact k_constant _ _, }
@[simp] lemma s_simp0 [pca α] (a b c : α) : ↓(𝐬 a b) * ↓c = (↓a * ↓c) * (↓b * ↓c) := by { rw ← s_simp, exact s_substitution _ _ _, }

def i [pca α] : α := 𝐬 k k
@[simp] lemma i_ident [pca α] (a : α) : ↓i * ↓a = ↓a := by { unfold i, simp, }
lemma itot [pca α] : tot (i : α) := by { intros x, simp, refl, }

lemma stot [pca α] : tot (s : α) := λ a, defined_l (stot' a a)

def subst' [pca α] (x : α) : α := option.get (stot x)
notation `𝐬'` := subst'

inductive lambda (α : Type u) [pca α]
| var : ℕ → lambda
| com : α → lambda
| app : lambda → lambda → lambda
prefix `#` := lambda.var
prefix `&`:max := lambda.com
instance lambda_mul (α : Type u) [pca α] : has_mul (lambda α) := ⟨lambda.app⟩

def lam [pca α] (n : ℕ) :lambda α → lambda α
| #m := if n = m then &i else &k * #m
| &c := &k * &c
| (l * k) := &s * (lam l) * (lam k)
notation `Λ`x`,` := lam x 

def expr [pca α] : lambda α → option α
| #x := ↓k
| &c := ↓c
| (l * k) := (expr l) * (expr k)

lemma lambda_defined [c : pca α] (n : ℕ) : ∀ (e : lambda α), defined (expr (Λ n, e) : option α)
| #e := begin
    cases (eq.decidable n e),
    { simp[lam, expr, if_neg h], exact rfl, },
    { simp[lam, expr, if_pos h], exact rfl, },
  end
| &c := ktot c
| (l * m) := begin
    simp [lam, expr], 
    let a := option.get (lambda_defined l),
    let b := option.get (lambda_defined m),
    have ha : expr (Λ n, l) = ↓a, { simp },
    have hb : expr (Λ n, m) = ↓b, { simp },
    rw [ha, hb],
    exact stot' a b
  end

notation n` ↦ `l := option.get (lambda_defined n l)

namespace recursion

def d [pca α] : α := 0 ↦ Λ 1, (#0 * #0 * #1)
def dd [pca α] : lambda α := Λ 0, (Λ 1, (#0 * #0 * #1))

lemma dtot [pca α] (f : α) : defined (d ⬝ f) :=
by { change (d ⬝ f) with (↓d * ↓f), unfold d, simp [lam, expr], exact rfl, }

lemma diagonal [pca α] (f x : α) : d ⬝ f * x = f ⬝ f * x :=
begin
  calc
    d ⬝ f * ↓x = ↓d * ↓f * ↓x : rfl
    ...        = f ⬝ f * ↓x   : by { unfold d, simp [lam, expr], refl, }
end

def v [pca α] : α := 0 ↦ Λ 1, (#0 * (&d * #1))
def n [pca α] : α := 0 ↦ &d * (&v * #0)

theorem recursion [pca α] (f : α) : n ⬝ f ≃ f * (n ⬝ f) :=
begin
  intros x,
  let vf := (0 ↦ &f * (&d * #0)),  
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
  let vf := (0 ↦ &f * (&d * #0)),  
  have hv : ↓v * ↓f = ↓vf, { unfold v, simp [lam, expr], },
  have nf_dvf : ↓n * ↓f = ↓d * ↓vf,  { unfold n, unfold v, simp [lam, expr], },
  rw nf_dvf,
  exact (dtot _)
end

end recursion

def fixpoint [pca α] : α := recursion.n
def recursion  [pca α] (f x : α) : ↓fixpoint * ↓f * ↓x = f * (↓fixpoint * ↓f) * ↓x := recursion.recursion f x
def fixpoint_of [pca α] (f : α) : α := option.get (recursion.ntot f)

end pca
