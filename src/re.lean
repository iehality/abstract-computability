import pca
import combinator

namespace pca

universe variable u
variables {α : Type u}

namespace set

inductive prec [pca α] (A : set α) : set α
| rel {a} : a ∈ A → prec a
| k : prec k
| s : prec s
| mul {a b c} : (↓a * ↓b) = ↓c → prec a → prec b → prec c
notation `ℰ` := prec
notation `ℰ₀` := prec ∅

def recursive (A : set α) [pca α] : set α := {x | x ∈ prec A ∧ tot x}
notation `ℛ` := recursive
notation `ℛ₀` := recursive ∅

lemma pr_subset [pca α] {A B : set α} {x : α} (hx : x ∈ ℰ A) (h : A ⊆ B) : x ∈ ℰ B :=
begin
  induction hx with a ha a b c e ha hb iha ihb,
  { exact prec.rel (h ha),},
  { exact prec.k, },
  { exact prec.s, },
  { exact prec.mul e iha ihb, },
end

lemma pr0_subset [pca α] {A : set α} {a : α} (ha : a ∈ (ℰ₀ : set α)) : a ∈ ℰ A :=
pr_subset ha (by { simp, })

lemma recuraive.k [pca α] (A : set α) : k ∈ ℛ A := ⟨prec.k, ktot⟩
lemma recuraive.s [pca α] (A : set α) : s ∈ ℛ A := ⟨prec.s, stot⟩

lemma prec.const (A : set α) [pca α] {a : α} : a ∈ (ℰ A : set α) → 𝐤 a ∈ (ℰ A : set α) :=
begin
  assume h : a ∈ ℰ A,
  have l0 : ↓k * ↓a = ↓𝐤 a, { simp, },
  show 𝐤 a ∈ ℰ A, from prec.mul l0 prec.k h,
end

lemma prec.subst [pca α] (A : set α) {a b : α} :
  a ∈ ℰ A → b ∈ ℰ A → 𝐬 a b ∈ ℰ A :=
begin
  assume (ha : a ∈ ℰ A) (hb : b ∈ ℰ A),
  have l0 : ↓s * ↓a = ↓𝐬' a, { unfold subst', simp, },
  have l1 : 𝐬' a ∈ (ℰ A : set α), from prec.mul l0 prec.s ha,
  have l2 : ↓𝐬' a * ↓b = ↓𝐬 a b, { unfold subst', simp, },
  show 𝐬 a b ∈ ℰ A, from prec.mul l2 l1 hb,
end

lemma prec.i [pca α] {A : set α} : i ∈ ℰ A := prec.subst A prec.k prec.k
lemma recursive.i [pca α] (A : set α) : i ∈ (ℛ A : set α) := ⟨prec.i, itot⟩

inductive lambdar [pca α] (A : set α) 
| var : ℕ → lambdar
| com {a : α} : a ∈ ℰ A → lambdar
| app : lambdar → lambdar → lambdar
prefix `#₀`:max := lambdar.var
prefix `&₀`:max := lambdar.com
notation `k₀` := &₀prec.k
notation `s₀` := &₀prec.s
notation `i₀` := &₀prec.i
instance lambdar_mul {A : set α} [pca α] : has_mul (lambdar A) := ⟨lambdar.app⟩

def lamr [pca α] {A : set α} (n : ℕ) : lambdar A → lambdar A
| #₀m     := if n = m then i₀ else k₀ * #₀m
| &₀h     := k₀ * lambdar.com h
| (l * m) := s₀ * (lamr l) * (lamr m)
notation `Λ₀`x`,` := lamr x 

def exprr [pca α] (A : set α): lambdar A → option α
| #₀x := ↓k
| (@lambdar.com _ _ _ e _) := ↓e
| (l * m) := (exprr l) * (exprr m)

lemma lambdar_defined [pca α] {A : set α} (n : ℕ) : ∀ (e : lambdar A), defined (exprr A (Λ₀ n, e))
| #₀e := begin
    cases (eq.decidable n e),
    { simp[lamr, exprr, if_neg h], exact rfl, },
    { simp[lamr, expr, if_pos h], exact rfl, },
  end
| (@lambdar.com _ _ _ e _) := ktot e
| (l * m) := begin
    simp [lamr, exprr], 
    let a := option.get (lambdar_defined l),
    let b := option.get (lambdar_defined m),
    have ha : exprr A (Λ₀ n, l) = ↓a, { simp },
    have hb : exprr A (Λ₀ n, m) = ↓b, { simp },
    rw [ha, hb],
    exact stot' a b
  end

notation n` -[`A`]→ ` l := option.get (@lambdar_defined _ _ A n l)

lemma lambdar_pr [pca α] {A : set α} :
  ∀ {e : lambdar A} (h : defined (exprr A e) = tt), option.get h ∈ (ℰ A : set α)
| #₀_ _ := prec.k
| &₀p _ := p
| (l * m) h := begin
    have ld : defined (exprr A l) = tt, from defined_l h,
    have md : defined (exprr A m) = tt, from defined_r h,
    have lpr : option.get ld ∈ ℰ A, from lambdar_pr ld,
    have mpr : option.get md ∈ ℰ A, from lambdar_pr md,
    have e : ↓option.get ld * ↓option.get md = ↓option.get h, { simp [exprr], },
    show option.get h ∈ ℰ A, from prec.mul e lpr mpr,
  end

lemma lambda_pr0 [pca α] {A : set α} (n : ℕ) (e : lambdar A) : (n -[A]→ e) ∈ (ℰ A : set α) := lambdar_pr _

namespace recursion_pr

def d [pca α] : α := 0 -[∅]→ (Λ₀ 1, (#₀0 * #₀0 * #₀1))
def dpr [pca α] : d ∈ (ℰ₀ : set α) := lambda_pr0 _ _

def v [pca α]: α := 0 -[∅]→ (Λ₀ 1, (#₀0 * (&₀dpr * #₀1)))
def vpr [pca α] : v ∈ (ℰ₀ : set α) := lambda_pr0 _ _

def n [pca α] : α := 0 -[∅]→ (&₀dpr * (&₀vpr * #₀0))
def npr [pca α] : n ∈ (ℰ₀ : set α) := lambda_pr0 _ _

lemma fixpoint_eq_n [pca α] : @fixpoint α _ = n :=
by { simp [fixpoint,recursion.n,n,recursion.d,recursion.v,d,v], refl, }

lemma fixpoint_pr [pca α] : fixpoint ∈ (ℰ₀ : set α) := by { rw fixpoint_eq_n, exact npr, }
lemma fixpoint_re [pca α] : fixpoint ∈ (ℛ₀ : set α) := ⟨fixpoint_pr, recursion.ntot⟩

end recursion_pr

class numbering (α : Type u) [pca α]
(code : α → ℕ)
(decode : ℕ → α)
(nat_pr : ∀ n : ℕ, decode n ∈ (ℰ₀ : set α))
(decode_code : ∀ x : α, x ∈ (ℰ₀ : set α) → decode (code x) = x)
(code_decode : ∀ n : ℕ, code (decode n) = n)

def Kl [pca α] : set α := {x : α | defined (↓x * ↓x)}
def K (A : set α) [pca α] := {x : α | x ∈ A ∧ defined (↓x * ↓x)}
def representable [pca α] (A : set α) : set (set α) := {B | ∃ e, e ∈ A ∧ B = {x | defined (↓e * ↓x)}}
notation A` is_representable_in `B := A ∈ representable B
def re_set [pca α] (A : set α) : Prop := ∃ e : α, e ∈ (ℰ₀ : set α) ∧ A = {x | defined (↓e * ↓x)}

lemma neg_p_iff_negp (P : Prop) : ¬(P ↔ ¬P) := 
begin
  rintros ⟨h₀, h₁⟩,
  have h₂ : ¬ P := λ p, h₀ p p,
  exact h₂ (h₁ h₂),
end

lemma K_re [pca α] : Kl is_representable_in (ℰ₀ : set α) :=
begin
  use (0 ↦ #0 * #0),
  have h : ∀ x : α, expr (Λ 0, (#0 * #0)) * ↓x = ↓x * ↓x, { intros x, simp [lam, expr], },
  split,
  { simp [lam, expr],
    show 𝐬 i i ∈ ℰ₀, from prec.subst _ prec.i prec.i, },
  apply set.ext,
  intros x,
  split,
  { assume xK, simp, rw h x, exact xK, },
  { unfold Kl, simp, assume xh, rw ← h x, exact xh, },
end

lemma compl_K_nre [pca α] : ¬ re_set (Klᶜ : set α) :=
begin
  rintro ⟨e, h⟩,
  apply neg_p_iff_negp (e ∈ (Kl : set α)),
  split,
  { assume eK : e ∈ Kl,
    show e ∈ (Klᶜ : set α), { rw h.2, simp, exact eK, }, },
  { assume nKc : e ∉ Kl,
    have eKc : e ∈ (Klᶜ : set α) := nKc,
    show e ∈ Kl, { unfold Kl, simp, rw h.2 at eKc, exact eKc, }, },
end

end set
end pca