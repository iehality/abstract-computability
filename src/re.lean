import pca
import combinator

namespace pca

universe variable u
variables {α : Type u}
variables [pca α]

inductive prec (A : set α) : set α
| rel {a} : a ∈ A → prec a
| k : prec k
| s : prec s
| mul {a b c} : (↓a * ↓b) = ↓c → prec a → prec b → prec c
notation `ℰ` := prec
notation `ℰ₀` := prec ∅

def recursive (A : set α) : set α := {x | x ∈ prec A ∧ tot x}
notation `ℛ` := recursive
notation `ℛ₀` := recursive ∅

@[simp] lemma pr_in_univ (a : α) : a ∈ ℰ (@set.univ α) := prec.rel (by simp)

lemma pr_subset {A B : set α} {x : α} (hx : x ∈ ℰ A) (h : A ⊆ B) : x ∈ ℰ B :=
begin
  induction hx with a ha a b c e ha hb iha ihb,
  { exact prec.rel (h ha),},
  { exact prec.k, },
  { exact prec.s, },
  { exact prec.mul e iha ihb, },
end

lemma pr0_subset {A : set α} {a : α} (ha : a ∈ (ℰ₀ : set α)) : a ∈ ℰ A :=
pr_subset ha (by { simp, })

lemma recuraive.k (A : set α) : k ∈ ℛ A := ⟨prec.k, ktot⟩
lemma recuraive.s (A : set α) : s ∈ ℛ A := ⟨prec.s, stot⟩

lemma prec.const (A : set α) {a : α} : a ∈ (ℰ A : set α) → 𝐤 a ∈ (ℰ A : set α) :=
begin
  assume h : a ∈ ℰ A,
  have l0 : ↓k * ↓a = ↓𝐤 a, { simp, },
  show 𝐤 a ∈ ℰ A, from prec.mul l0 prec.k h,
end

lemma prec.subst (A : set α) {a b : α} :
  a ∈ ℰ A → b ∈ ℰ A → 𝐬 a b ∈ ℰ A :=
begin
  assume (ha : a ∈ ℰ A) (hb : b ∈ ℰ A),
  have l0 : ↓s * ↓a = ↓𝐬' a, { unfold subst', simp, },
  have l1 : 𝐬' a ∈ (ℰ A : set α), from prec.mul l0 prec.s ha,
  have l2 : ↓𝐬' a * ↓b = ↓𝐬 a b, { unfold subst', simp, },
  show 𝐬 a b ∈ ℰ A, from prec.mul l2 l1 hb,
end

lemma prec.i {A : set α} : i ∈ ℰ A := prec.subst A prec.k prec.k
lemma recursive.i (A : set α) : i ∈ (ℛ A : set α) := ⟨prec.i, itot⟩

inductive lambdar (A : set α) 
| var : ℕ → lambdar
| com {a : α} : a ∈ ℰ A → lambdar
| app : lambdar → lambdar → lambdar
prefix `#`:max := lambdar.var
prefix `&`:max := lambdar.com

instance lambdar_mul {A : set α} : has_mul (lambdar A) := ⟨lambdar.app⟩

def lam {A : set α} (n : ℕ) : lambdar A → lambdar A
| #m     := if n = m then &prec.i else &prec.k * #m
| &h     := &prec.k * lambdar.com h
| (l * m) := &prec.s * (lam l) * (lam m)
notation `Λ`x`,` := lam x 

def expr (A : set α): lambdar A → option α
| #x := ↓k
| (@lambdar.com _ _ _ e _) := ↓e
| (l * m) := (expr l) * (expr m)

lemma lambdar_defined {A : set α} (n : ℕ) : ∀ (e : lambdar A), defined (expr A (Λ n, e))
| #e := begin
    cases (eq.decidable n e),
    { simp[lam, expr, if_neg h], exact rfl, },
    { simp[lam, expr, if_pos h], exact rfl, },
  end
| (@lambdar.com _ _ _ e _) := ktot e
| (l * m) := begin
    simp [lam, expr], 
    let a := option.get (lambdar_defined l),
    let b := option.get (lambdar_defined m),
    have ha : expr A (Λ n, l) = ↓a, { simp },
    have hb : expr A (Λ n, m) = ↓b, { simp },
    rw [ha, hb],
    exact stot' a b
  end

notation n` →[`A`] `l := option.get (@lambdar_defined _ _ A n l)
notation n` →∅ `l := n →[∅] l
notation n` →u `l := n →[set.univ] l


lemma lambdar_pr {A : set α} :
  ∀ {e : lambdar A} (h : defined (expr A e) = tt), option.get h ∈ ℰ A
| #_ _ := prec.k
| &p _ := p
| (l * m) h := begin
    have ld : defined (expr A l) = tt, from defined_l h,
    have md : defined (expr A m) = tt, from defined_r h,
    have lpr : option.get ld ∈ ℰ A, from lambdar_pr ld,
    have mpr : option.get md ∈ ℰ A, from lambdar_pr md,
    have e : ↓option.get ld * ↓option.get md = ↓option.get h, { simp [expr], },
    show option.get h ∈ ℰ A, from prec.mul e lpr mpr,
  end

@[simp] lemma lambda_pr0 {A : set α} (n : ℕ) (e : lambdar A) : (n →[A] e) ∈ ℰ A := lambdar_pr _

namespace recursion

def d : α := 0 →∅ (Λ 1, (#0 * #0 * #1))
def dpr : d ∈ (ℰ₀ : set α) := lambda_pr0 _ _

def v: α := 0 →∅ (Λ 1, (#0 * (&dpr * #1)))
def vpr : v ∈ (ℰ₀ : set α) := lambda_pr0 _ _

def n : α := 0 →∅ (&dpr * (&vpr * #0))
def npr : n ∈ (ℰ₀ : set α) := lambda_pr0 _ _

theorem recursion (f : α) : n ⬝ f ≃ ↓f * (n ⬝ f) :=
begin
  intros x,
  have diagonal : ∀ g, ↓d * ↓g * ↓x = ↓g * ↓g * ↓x, { unfold d, simp [lam, expr], },
  let vf := (0 →u &(pr_in_univ f) * (&(pr_in_univ d) * #0)),  
  have hv : ↓v * ↓f = ↓vf, { unfold v, simp [lam, expr], },
  have nf_dvf : ↓n * ↓f = ↓d * ↓vf,  { unfold n, unfold v, simp [lam, expr], },
  calc
    n ⬝ f * ↓x = ↓n * ↓f * ↓x         : rfl
    ...        = ↓d * ↓vf * ↓x        : by { rw nf_dvf, }
    ...        = ↓vf * ↓vf * ↓x       : diagonal vf
    ...        = ↓f * (↓d * ↓vf) * ↓x : by { simp [lam, expr], }
    ...        = ↓f * (↓n * ↓f) * ↓x  : by { rw nf_dvf, }
end

theorem ntot : tot (n : α) :=
begin
  intros f,
  let vf := (0 →u &(pr_in_univ f) * (&(pr_in_univ d) * #0)),  
  have hv : ↓v * ↓f = ↓vf, { unfold v, simp [lam, expr], },
  have nf_dvf : ↓n * ↓f = ↓d * ↓vf,  { unfold n, unfold v, simp [lam, expr], },
  have dtot : tot (d : α), { intros x, simp [d, lam, expr], refl, },
  rw nf_dvf,
  exact (dtot vf),
end

end recursion

def fixpoint : α := recursion.n
def recursion  (f x : α) : ↓fixpoint * ↓f * ↓x = f * (↓fixpoint * ↓f) * ↓x := recursion.recursion f x
def fixpoint_of (f : α) : α := option.get (recursion.ntot f)

lemma fixpoint_pr : fixpoint ∈ (ℰ₀ : set α) := recursion.npr
lemma fixpoint_re : fixpoint ∈ (ℛ₀ : set α) := ⟨fixpoint_pr, recursion.ntot⟩

namespace nontotal

variables [nontotal α]

def divergent_u : α := 0 →u &(pr_in_univ nontotal.p) * &(pr_in_univ nontotal.q)


end nontotal

def reducible (A : set α) (f g : α) : Prop := ∃ e : α, e ∈ ℰ A ∧ ↓e * ↓g = ↓f 
def T_reducible (f g : α) : Prop := reducible ∅ f g
infix ` ≤_T `:80 := T_reducible
infix ` ≡_T `:80 := λ f g, f ≤_T g ∧ g ≤_T f

@[refl] lemma T_reducible.refl (a : α) : a ≤_T a :=
by { use i, split, exact prec.i, simp, }

@[trans] lemma T_reducible.trans (a b c : α) (hab : a ≤_T b) (hbc : b ≤_T c) : a ≤_T c :=
begin
  rcases hab with ⟨e_ab, ⟨e_ab_pr, heab⟩⟩,
  rcases hbc with ⟨e_bc, ⟨e_bc_pr, hebc⟩⟩,
  let e_ac := (0 →∅ &e_ab_pr * (&e_bc_pr * #0)),
  use e_ac,
  split,
  { show e_ac ∈ ℰ₀, simp, },
  { show ↓e_ac * ↓c = ↓a, simp [lam, expr, heab, hebc], },
end

namespace jump
/-
def jump_pred (A : set α) (j : α) : Prop := 
(∀ x, x ∈ ℰ A → ↓j * ↓x = ↓(if defined (↓x * ↓x) then combinator.top else combinator.bot))
theorem jhjhj (A : set α) (j : α) (hj : jump_pred A j) : j ∉ ℰ A :=
begin
  assume h : j ∈ ℰ A,
  let 
end 
-/
end jump

end pca