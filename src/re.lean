import pca

namespace pca

universe variable u
variables {α : Type u}
variables [pca α]

/- Minimum submodel of pca containing A -/
inductive submodel (A : set α) : set α
| rel {a} : a ∈ A → submodel a
| k : submodel k
| s : submodel s
| mul {a b c} : (↓a * ↓b) = ↓c → submodel a → submodel b → submodel c
notation `ℳ` := submodel
notation `ℳ₀` := submodel ∅

def recursive (A : set α) : set α := {x | x ∈ submodel A ∧ tot x}
notation `ℛ` := recursive
notation `ℛ₀` := recursive ∅

@[simp] lemma pr_in_univ (a : α) : a ∈ ℳ (@set.univ α) := submodel.rel (by simp)

lemma pr_subset {A B : set α} {x : α} (hx : x ∈ ℳ A) (h : A ⊆ B) : x ∈ ℳ B :=
begin
  induction hx,
  case submodel.rel : a ha
  { exact submodel.rel (h ha),},
  case submodel.k :
  { exact submodel.k, },
  case submodel.s :
  { exact submodel.s, },
  case submodel.mul : _ _ _ e _ _ iha ihb
  { exact submodel.mul e iha ihb, },
end

lemma pr0_subset {A : set α} {a : α} (ha : a ∈ (ℳ₀ : set α)) : a ∈ ℳ A :=
pr_subset ha (by { simp, })

lemma recuraive.k (A : set α) : k ∈ ℛ A := ⟨submodel.k, ktot⟩
lemma recuraive.s (A : set α) : s ∈ ℛ A := ⟨submodel.s, stot⟩

lemma submodel.const {A : set α} {a : α} : a ∈ (ℳ A : set α) → 𝚔 a ∈ (ℳ A : set α) :=
begin
  assume h : a ∈ ℳ A,
  have l0 : ↓k * ↓a = ↓𝚔 a, { simp, },
  show 𝚔 a ∈ ℳ A, from submodel.mul l0 submodel.k h,
end

lemma submodel.subst' {A : set α} {a : α} :
  a ∈ ℳ A → 𝚜' a ∈ ℳ A :=
begin
  assume h : a ∈ ℳ A,
  have l0 : ↓s * ↓a = ↓𝚜' a, { unfold subst', simp, },
  show 𝚜' a ∈ ℳ A, from submodel.mul l0 submodel.s h,
end

lemma submodel.subst {A : set α} {a b : α} :
  a ∈ ℳ A → b ∈ ℳ A → 𝚜 a b ∈ ℳ A :=
begin
  assume (ha : a ∈ ℳ A) (hb : b ∈ ℳ A),
  have l0 : 𝚜' a ∈ (ℳ A : set α), from submodel.subst' ha,
  have l1 : ↓𝚜' a * ↓b = ↓𝚜 a b, { unfold subst', simp, },
  show 𝚜 a b ∈ ℳ A, from submodel.mul l1 l0 hb,
end

@[simp] lemma submodel.i {A : set α} : i ∈ ℳ A := submodel.subst submodel.k submodel.k
@[simp] lemma recursive.i (A : set α) : i ∈ (ℛ A : set α) := ⟨submodel.i, itot⟩

inductive lambda (A : set α) 
| var : ℕ → lambda
| com {a : α} : a ∈ ℳ A → lambda
| app : lambda → lambda → lambda
prefix `#`:max := lambda.var
prefix `&`:max := lambda.com

instance lambda_mul {A : set α} : has_mul (lambda A) := ⟨lambda.app⟩

def lam {A : set α} (n : ℕ) : lambda A → lambda A
| #m     := if n = m then &submodel.i else &submodel.k * #m
| &h     := &submodel.k * lambda.com h
| (l * m) := &submodel.s * (lam l) * (lam m)
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
  ∀ {e : lambda A} (h : defined (expr A e) = tt), option.get h ∈ ℳ A
| #_ _ := submodel.k
| &p _ := p
| (l * m) h := begin
    have ld : defined (expr A l) = tt, from str_l h,
    have md : defined (expr A m) = tt, from str_r h,
    have lpr : option.get ld ∈ ℳ A, from lambda_pr ld,
    have mpr : option.get md ∈ ℳ A, from lambda_pr md,
    have e : ↓option.get ld * ↓option.get md = ↓option.get h, { simp [expr], },
    show option.get h ∈ ℳ A, from submodel.mul e lpr mpr,
  end

@[simp] lemma lambda_pr0 {A : set α} (n : ℕ) (e : lambda A) : (n →[A] e) ∈ ℳ A := lambda_pr _

namespace recursion

def d : α := 0 →∅ (Λ 1, (#0 * #0 * #1))
def dpr : d ∈ (ℳ₀ : set α) := lambda_pr0 _ _

def v: α := 0 →∅ (Λ 1, (#0 * (&dpr * #1)))
def vpr : v ∈ (ℳ₀ : set α) := lambda_pr0 _ _

def n : α := 0 →∅ (&dpr * (&vpr * #0))
def npr : n ∈ (ℳ₀ : set α) := lambda_pr0 _ _

theorem recursion (f : α) : n ⬝ f ≃ ↓f * (n ⬝ f) :=
begin
  intros x,
  have diagonal : ∀ g, ↓d * ↓g * ↓x = ↓g * ↓g * ↓x, { simp [d, lam, expr], },
  let vf := (0 →u &(pr_in_univ f) * (&(pr_in_univ d) * #0)),  
  have hv : ↓v * ↓f = ↓vf, { simp [v, lam, expr], },
  have nf_dvf : ↓n * ↓f = ↓d * ↓vf,  { simp [n, v, lam, expr], },
  calc
    n ⬝ f * ↓x = ↓n * ↓f * ↓x         : rfl
    ...        = ↓d * ↓vf * ↓x        : by rw nf_dvf
    ...        = ↓vf * ↓vf * ↓x       : diagonal vf
    ...        = ↓f * (↓d * ↓vf) * ↓x : by simp [lam, expr]
    ...        = ↓f * (↓n * ↓f) * ↓x  : by rw nf_dvf
end

theorem ntot : tot (n : α) := by { intros f, simp [n, d, v, lam, expr], refl, }

end recursion

def fixpoint : α := recursion.n
def recursion  (f x : α) : ↓fixpoint * ↓f * ↓x = f * (↓fixpoint * ↓f) * ↓x := recursion.recursion f x
def fixpoint_of (f : α) : α := option.get (recursion.ntot f)

lemma fixpoint_pr : fixpoint ∈ (ℳ₀ : set α) := recursion.npr
lemma fixpoint_re : fixpoint ∈ (ℛ₀ : set α) := ⟨fixpoint_pr, recursion.ntot⟩

namespace nontotal

def nontotal_in (A : set α) : Prop := ∃ p q, (↓p * ↓q = none ∧ p ∈ ℳ A ∧ q ∈ ℳ A)

theorem nontot_iff_diff (A : set α) :
  (nontotal_in A) ↔ (∃ e, (e ∈ ℳ A ∧ ∀ x, (x ∈ ℳ A → ↓e * ↓x ≠ ↓x))) :=
begin
  split,
  { rintros ⟨p, ⟨q, ⟨epq, ⟨ppr, qpr⟩⟩⟩⟩,
    let e := (0 →[A] &ppr * &qpr),
    use e,
    split,
    { show e ∈ ℳ A, simp, },
    { show ∀ x, x ∈ ℳ A → ↓e * ↓x ≠ ↓x, simp[lam, expr, epq], }, },
  { rintros ⟨e, ⟨epr, h⟩⟩,
    let f := (0 →[A] &epr * (#0 * #0)),
    have fpr : f ∈ ℳ A, { simp, },
    have hf0 : ∀ g, ↓f * ↓g = ↓e * (↓g * ↓g), { intros g, simp[lam, expr], },
    have hf1 : ↓e * (↓f * ↓f) = ↓f * ↓f, { symmetry, exact hf0 _, },
    use f, use f,
    split,
    { cases ef : ↓f * ↓f,
      case none : { refl, },
      case some : v
      { exfalso,
        have vpr : v ∈ ℳ A, from submodel.mul ef fpr fpr,
        show false, from h v vpr (by { rw ← ef, exact hf1, }), }, },
    { exact ⟨fpr, fpr⟩, }, },
end

theorem nontotal_neg_totalin_or_neg_extin [nontotal α] (A : set α) :
  ¬total_in (ℳ A) ∨ ¬extensional_in (ℳ A) :=
begin
  apply not_and_distrib.mp,
  rintros ⟨h0 : total_in (ℳ A), h1 : extensional_in (ℳ A)⟩,
  have e0 : (𝚜' k : α) = 𝚔 i,
  { apply h1,
    { show 𝚜' k ∈ ℳ A, from submodel.subst' submodel.k, },
    { show 𝚔 i ∈ ℳ A, from submodel.const submodel.i, },
    { intros x xpr,
      simp,
      apply h1,
      { show 𝚜 k x ∈ ℳ A, from submodel.subst submodel.k xpr, },
      { show i ∈ ℳ A, from submodel.i, },
      intros y ypr,
      calc
        ↓𝚜 k x * ↓y = ↓𝚔 y * ↓option.get (h0 xpr ypr) : by simp
        ...         = ↓i * ↓y : by simp only [k_simp0, i_simp], }, },
  have e1 : ↓(𝚔 div1 : α) * (↓div0 * ↓div1) = ↓div1,
  { calc
      ↓(𝚔 div1 : α) * (↓div0 * ↓div1) = ↓𝚜' k * ↓div0 * ↓div1 : by simp
      ...                             = ↓𝚔 i * ↓div0 * ↓div1  : by rw e0
      ...                             = ↓div1                 : by simp, },
  have hd : defined (↓(𝚔 div1 : α) * (↓div0 * ↓div1)) = tt, { rw e1, refl, },
  have c0 : defined (↓div0 * ↓div1 : option α) = tt, from str_r hd,
  have c1 : defined (↓div0 * ↓div1 : option α) = ff, simp,
  show false, from bool_iff_false.mpr c1 c0
end

end nontotal

end pca