import data.option.basic
import tactic
--import data.real.basic

universe variable u

variables {α : Type u}

class partial_magma (α : Type u) :=
(mul : α → α → option α)
infixl ` ⬝ ` := partial_magma.mul
infix ` ↓= `:50 := λ x y, x = some y
prefix `↓`:80 := some

def partial_magma.mmul [partial_magma α] : option α → option α → option α
| ↓x ↓y := x ⬝ y
| none _ := none
| _ none := none
instance pm_mul [c : partial_magma α] : has_mul (option α) := {mul := @partial_magma.mmul _ c}

/- Partial Combinatory Algebra -/
class pca (α : Type u) extends partial_magma α :=
(k : α)
(ktot : ∀ x, option.is_some (k ⬝ x))
(k_constant : ∀ x y : α, k ⬝ x * y = x)
(s : α)
(stot : ∀ x y : α, option.is_some (s ⬝ x * y))
(s_substitution : ∀ x y z : α, s ⬝ x * y * z = (x ⬝ z) * (y ⬝ z))

def pca.equiv [partial_magma α] (a b : option α) : Prop := ∀ x : α, a * ↓x = b * ↓x
infix ` ≃ `:50 := pca.equiv 

namespace pca

def const [pca α] (x : α) := option.get (ktot x)
def subst [pca α] (x y : α) := option.get (stot x y)
notation `𝐤` := const
notation `𝐬` := subst

lemma k_constant_ [c : pca α] : ∀ x y : α, k ⬝ x * ↓y = ↓x := c.k_constant
lemma s_substitution_ [c : pca α] : ∀ x y z : α, s ⬝ x * ↓y * ↓z = (x ⬝ z) * (y ⬝ z) := c.s_substitution
lemma s_substitution_0 [c : pca α] : ∀ x y z : α, ↓s * ↓x * ↓y * ↓z = (x ⬝ z) * (y ⬝ z) := c.s_substitution
lemma k_compute [pca α] (x : α) : k ⬝ x = ↓(𝐤 x) := by { unfold const, simp }
lemma s_compute [pca α] (x y : α) : s ⬝ x * ↓y = ↓(𝐬 x y) := by { unfold subst, simp, refl }


lemma constant_simp [pca α] (a b : α) : 𝐤 a ⬝ b ↓= a :=
begin
  have e : (k ⬝ a : option α) = ↓(𝐤 a), { unfold const, simp },
  calc
    𝐤 a ⬝ b = k ⬝ a * ↓b : by { rw e, refl }
    ...     = ↓a           : k_constant _ _
end

lemma substitution_simp [pca α] (a b c : α) : 𝐬 a b ⬝ c = a ⬝ c * b ⬝ c :=
begin
  have e : (s ⬝ a * ↓b : option α) = ↓(𝐬 a b), { unfold subst, simp, refl },
  calc
    𝐬 a b ⬝ c = s ⬝ a * ↓b * ↓c : by { rw e, refl }
    ...       = a ⬝ c * b ⬝ c           : s_substitution _ _ _
end

def i [pca α] : α := 𝐬 k k

lemma i_ident [pca α] (x : α) : i ⬝ x ↓= x :=
begin
  calc
    i ⬝ x = (𝐬 k k) ⬝ x       : by { unfold i, }
    ...   = k ⬝ x * k ⬝ x     : by { simp only [substitution_simp], }
    ...   = k ⬝ x * (↓(𝐤 x)) : by { unfold const, simp, }
    ...   = ↓x               : by { simp only [k_constant_], }
end

@[simp] lemma k_compute0 [pca α] (a : α) : ↓k * ↓a = ↓(𝐤 a) := k_compute a
@[simp] lemma s_compute0 [pca α] (a b : α) : ↓s * ↓a * ↓b = ↓(𝐬 a b) := s_compute a b
@[simp] lemma k_simp [pca α] (a b : α) : ↓(𝐤 a) * ↓b = ↓a := constant_simp a b
@[simp] lemma s_simp [pca α] (a b c : α) : ↓(𝐬 a b) * ↓c = (↓a * ↓c) * (↓b * ↓c) := substitution_simp a b c
@[simp] lemma i_simp [pca α ] (a : α) : ↓i * ↓a = ↓a := i_ident a

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

def code [pca α] : lambda α → option α
| (var x) := ↓k
| (com c) := ↓c
| (l * k) := (code l) * (code k)

lemma lambda_defined [c : pca α] : ∀ (n : ℕ) (e : lambda α), option.is_some (code (Λ n, e) : option α)
| n (var e) := begin
    cases (eq.decidable n e),
    { have he : (Λ n, (var e) : @lambda _ c) = com k * var e, { simp [lam], intros, contradiction },
      rw he,
      exact ktot _ },
    { have he : (Λ n, (var e) : @lambda _ c) = com i, { simp [lam], intros, contradiction },
      rw he,
      exact rfl, }
  end
| n (com c) := ktot c
| n (l * m) := begin
    simp [lam, code], 
    let a := option.get (lambda_defined n l),
    let b := option.get (lambda_defined n m),
    have ha : code (Λ n, l) = ↓a, { simp },
    have hb : code (Λ n, m) = ↓b, { simp },
    rw [ha, hb],
    exact stot a b
  end

namespace recursionthm

def d [pca α] : α := option.get (lambda_defined 0 (Λ 1, (var 0 * var 0 * var 1)))

lemma dtot [pca α] (f : α) : option.is_some (d ⬝ f) :=
begin
  have e : d ⬝ f = code (Λ 0, (com f * com f * var 0)),
  { change (d ⬝ f) with (↓d * ↓f), unfold d, simp [lam, code], },
  rw e,
  exact (lambda_defined 0 _),
end

lemma diagonal [pca α] (f x : α) : d ⬝ f * x = f ⬝ f * x :=
begin
  calc
    d ⬝ f * ↓x = ↓d * ↓f * ↓x                                      :rfl
    ...       = code (Λ 0, (Λ 1, (var 0 * var 0 * var 1))) * ↓f * ↓x : by { unfold d, simp, }
    ...       = f ⬝ f * ↓x                                            : by { simp [lam, code], refl, }
end

def v [pca α] : α := option.get (lambda_defined 0 (Λ 1, (var 0 * (com d * var 1))))
def n [pca α] : α := option.get (lambda_defined 0 (com d * (com v * var 0)))

theorem recursion [pca α] (f : α) : n ⬝ f ≃ f * (n ⬝ f) :=
begin
  intros x,
  let vf := option.get (lambda_defined 0 (com f * (com d * var 0))),  
  have hv : ↓v * ↓f ↓= vf, { unfold v, simp [lam, code], },
  have nf_dvf : ↓n * ↓f = ↓d * ↓vf,
  { calc
      ↓n * ↓f = code (Λ 0, (com d * (com v * var 0))) * ↓f : by { unfold n, simp, }
      ...       = ↓d * ↓vf                                  : by { rw ← hv, simp [lam, code], } },
  calc
    n ⬝ f * x = ↓n * ↓f * x          : rfl
    ...       = ↓d * ↓vf * x         : by { rw nf_dvf, }
    ...       = ↓vf * ↓vf * x        : diagonal vf x
    ...       = ↓f * (↓d * ↓vf) * x : by { simp [lam, code], }
    ...       = ↓f * (↓n * ↓f) * x  : by { rw nf_dvf, }
end

theorem fixpoint_def [pca α] (f : α) : option.is_some (n ⬝ f) :=
begin
  let vf := option.get (lambda_defined 0 (com f * (com d * var 0))),  
  have hv : ↓v * ↓f = ↓vf, { unfold v, simp [lam, code], },
  have nf_dvf : n ⬝ f = ↓d * ↓vf,
  { calc
      ↓n * ↓f = code (Λ 0, (com d * (com v * var 0))) * ↓f : by { unfold n, simp, }
      ...       = ↓d * ↓vf                                  : by { rw ← hv, simp [lam, code], } },
  rw nf_dvf,
  exact (dtot _)
end

end recursionthm

def fixpoint [pca α] : α := recursionthm.n
def recursion  [pca α] (f : α) : fixpoint ⬝ f ≃ f * (fixpoint ⬝ f) := recursionthm.recursion f

end pca
