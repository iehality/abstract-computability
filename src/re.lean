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
  induction hx,
  case prec.rel : a ha
  { exact prec.rel (h ha),},
  case prec.k :
  { exact prec.k, },
  case prec.s :
  { exact prec.s, },
  case prec.mul : _ _ _ e _ _ iha ihb
  { exact prec.mul e iha ihb, },
end

lemma pr0_subset {A : set α} {a : α} (ha : a ∈ (ℰ₀ : set α)) : a ∈ ℰ A :=
pr_subset ha (by { simp, })

lemma recuraive.k (A : set α) : k ∈ ℛ A := ⟨prec.k, ktot⟩
lemma recuraive.s (A : set α) : s ∈ ℛ A := ⟨prec.s, stot⟩

lemma prec.const {A : set α} {a : α} : a ∈ (ℰ A : set α) → 𝐤 a ∈ (ℰ A : set α) :=
begin
  assume h : a ∈ ℰ A,
  have l0 : ↓k * ↓a = ↓𝐤 a, { simp, },
  show 𝐤 a ∈ ℰ A, from prec.mul l0 prec.k h,
end

lemma prec.subst' {A : set α} {a : α} :
  a ∈ ℰ A → 𝐬' a ∈ ℰ A :=
begin
  assume h : a ∈ ℰ A,
  have l0 : ↓s * ↓a = ↓𝐬' a, { unfold subst', simp, },
  show 𝐬' a ∈ ℰ A, from prec.mul l0 prec.s h,
end

lemma prec.subst {A : set α} {a b : α} :
  a ∈ ℰ A → b ∈ ℰ A → 𝐬 a b ∈ ℰ A :=
begin
  assume (ha : a ∈ ℰ A) (hb : b ∈ ℰ A),
  have l0 : 𝐬' a ∈ (ℰ A : set α), from prec.subst' ha,
  have l1 : ↓𝐬' a * ↓b = ↓𝐬 a b, { unfold subst', simp, },
  show 𝐬 a b ∈ ℰ A, from prec.mul l1 l0 hb,
end

@[simp] lemma prec.i {A : set α} : i ∈ ℰ A := prec.subst prec.k prec.k
@[simp] lemma recursive.i (A : set α) : i ∈ (ℛ A : set α) := ⟨prec.i, itot⟩

inductive lambda (A : set α) 
| var : ℕ → lambda
| com {a : α} : a ∈ ℰ A → lambda
| app : lambda → lambda → lambda
prefix `#`:max := lambda.var
prefix `&`:max := lambda.com

instance lambda_mul {A : set α} : has_mul (lambda A) := ⟨lambda.app⟩

def lam {A : set α} (n : ℕ) : lambda A → lambda A
| #m     := if n = m then &prec.i else &prec.k * #m
| &h     := &prec.k * lambda.com h
| (l * m) := &prec.s * (lam l) * (lam m)
notation `Λ`x`,` := lam x 

def expr (A : set α): lambda A → option α
| #x := ↓k
| (@lambda.com _ _ _ e _) := ↓e
| (l * m) := (expr l) * (expr m)

lemma lambda_defined {A : set α} (n : ℕ) : ∀ (e : lambda A), defined (expr A (Λ n, e))
| #e := begin
    cases (eq.decidable n e),
    { simp[lam, expr, if_neg h], exact rfl, },
    { simp[lam, expr, if_pos h], exact rfl, },
  end
| (@lambda.com _ _ _ e _) := ktot e
| (l * m) := begin
    simp [lam, expr], 
    let a := option.get (lambda_defined l),
    let b := option.get (lambda_defined m),
    have ha : expr A (Λ n, l) = ↓a, { simp },
    have hb : expr A (Λ n, m) = ↓b, { simp },
    rw [ha, hb],
    exact s_defined a b
  end

notation n` →[`A`] `l := option.get (@lambda_defined _ _ A n l)
notation n` →∅ `l := n →[∅] l
notation n` →u `l := n →[set.univ] l

lemma lambda_pr {A : set α} :
  ∀ {e : lambda A} (h : defined (expr A e) = tt), option.get h ∈ ℰ A
| #_ _ := prec.k
| &p _ := p
| (l * m) h := begin
    have ld : defined (expr A l) = tt, from str_l h,
    have md : defined (expr A m) = tt, from str_r h,
    have lpr : option.get ld ∈ ℰ A, from lambda_pr ld,
    have mpr : option.get md ∈ ℰ A, from lambda_pr md,
    have e : ↓option.get ld * ↓option.get md = ↓option.get h, { simp [expr], },
    show option.get h ∈ ℰ A, from prec.mul e lpr mpr,
  end

@[simp] lemma lambda_pr0 {A : set α} (n : ℕ) (e : lambda A) : (n →[A] e) ∈ ℰ A := lambda_pr _

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
  have diagonal : ∀ g, ↓d * ↓g * ↓x = ↓g * ↓g * ↓x, { simp [d, lam, expr], },
  let vf := (0 →u &(pr_in_univ f) * (&(pr_in_univ d) * #0)),  
  have hv : ↓v * ↓f = ↓vf, { simp [v, lam, expr], },
  have nf_dvf : ↓n * ↓f = ↓d * ↓vf,  { simp [n, v, lam, expr], },
  calc
    n ⬝ f * ↓x = ↓n * ↓f * ↓x         : rfl
    ...        = ↓d * ↓vf * ↓x        : by { rw nf_dvf, }
    ...        = ↓vf * ↓vf * ↓x       : diagonal vf
    ...        = ↓f * (↓d * ↓vf) * ↓x : by { simp [lam, expr], }
    ...        = ↓f * (↓n * ↓f) * ↓x  : by { rw nf_dvf, }
end

theorem ntot : tot (n : α) := by { intros f, simp [n, d, v, lam, expr], refl, }

end recursion

def fixpoint : α := recursion.n
def recursion  (f x : α) : ↓fixpoint * ↓f * ↓x = f * (↓fixpoint * ↓f) * ↓x := recursion.recursion f x
def fixpoint_of (f : α) : α := option.get (recursion.ntot f)

lemma fixpoint_pr : fixpoint ∈ (ℰ₀ : set α) := recursion.npr
lemma fixpoint_re : fixpoint ∈ (ℛ₀ : set α) := ⟨fixpoint_pr, recursion.ntot⟩

namespace nontotal
structure and (a b : Prop) : Prop :=
intro :: (left : a) (right : b)

def nontotal_in (A : set α) : Prop := ∃ p q, (↓p * ↓q = none ∧ p ∈ ℰ A ∧ q ∈ ℰ A)

theorem nontot_iff_diff (A : set α) :
  (nontotal_in A) ↔ (∃ e, (e ∈ ℰ A ∧ ∀ x, (x ∈ ℰ A → ↓e * ↓x ≠ ↓x))) :=
begin
  split,
  { rintros ⟨p, ⟨q, ⟨epq, ⟨ppr, qpr⟩⟩⟩⟩,
    let e := (0 →[A] &ppr * &qpr),
    use e,
    split,
    { show e ∈ ℰ A, simp, },
    { show ∀ x, x ∈ ℰ A → ↓e * ↓x ≠ ↓x, simp[lam, expr, epq], }, },
  { rintros ⟨e, ⟨epr, h⟩⟩,
    let f := (0 →[A] &epr * (#0 * #0)),
    have fpr : f ∈ ℰ A, { simp, },
    have hf0 : ∀ g, ↓f * ↓g = ↓e * (↓g * ↓g), { intros g, simp[lam, expr], },
    have hf1 : ↓e * (↓f * ↓f) = ↓f * ↓f, { symmetry, exact hf0 _, },
    use f, use f,
    split,
    { cases ef : ↓f * ↓f,
      case none : { refl, },
      case some : v
      { exfalso,
        have vpr : v ∈ ℰ A, from prec.mul ef fpr fpr,
        show false, from h v vpr (by { rw ← ef, exact hf1, }), }, },
    { exact ⟨fpr, fpr⟩, }, },
end

lemma nhbcdkjsvk (P Q : Prop) : ¬(P ∧ Q) → (¬P ∨ ¬Q) := by { exact not_and_distrib.mp}

theorem total_ext [nontotal α] (A : set α) : ¬total_in (ℰ A) ∨ ¬extensional_in (ℰ A) :=
begin
  apply not_and_distrib.mp,
  rintros ⟨h0 : total_in (ℰ A), h1 : extensional_in (ℰ A)⟩,
  have e0 : (𝐬' k : α) = 𝐤 i,
  { apply h1,
    { show 𝐬' k ∈ ℰ A, from prec.subst' prec.k, },
    { show 𝐤 i ∈ ℰ A, from prec.const prec.i, },
    { intros x xpr,
      simp,
      apply h1,
      { show 𝐬 k x ∈ ℰ A, from prec.subst prec.k xpr, },
      { show i ∈ ℰ A, from prec.i, },
      intros y ypr,
      calc
        ↓𝐬 k x * ↓y = ↓𝐤 y * ↓option.get (h0 xpr ypr) : by simp
        ...         = ↓i * ↓y : by simp only [k_simp0, i_simp], }, },
  have e1 : ↓(𝐤 div1 : α) * (↓div0 * ↓div1) = ↓div1,
  { calc
    ↓(𝐤 div1 : α) * (↓div0 * ↓div1) = ↓𝐬' k * ↓div0 * ↓div1 : by simp
    ...                             = ↓𝐤 i * ↓div0 * ↓div1  : by rw e0
    ...                             = ↓div1                 : by simp, },
  have hd : defined (↓(𝐤 div1 : α) * (↓div0 * ↓div1)) = tt, { rw e1, refl, },
  have c0 : defined (↓div0 * ↓div1 : option α) = tt, from str_r hd,
  have c1 : defined (↓div0 * ↓div1 : option α) = ff, simp,
  show false, from bool_iff_false.mpr c1 c0
end

end nontotal

namespace reduciability

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

end reduciability

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