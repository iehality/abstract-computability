import data.option.basic
import tactic

universe variable u
variables {α : Type u}

class pmagma (α : Type u) :=
(mul : α → α → option α)
infixl ` ⬝ ` := pmagma.mul
infix ` ↓= `:50 := λ x y, x = some y
prefix `↓`:80 := some

abbreviation defined : option α → bool := option.is_some
abbreviation udefined : option α → bool := option.is_none

def pmagma.mmul [pmagma α] : option α → option α → option α
| ↓x ↓y := x ⬝ y
| _ _   := none
instance pm_mul [pmagma α] : has_mul (option α) := {mul := @pmagma.mmul α _}

@[simp] lemma pmagma.none_l [pmagma α] (p : option α) : none * p = none := option.cases_on p rfl (λ _, rfl)
@[simp] lemma pmagma.none_r [pmagma α] (p : option α) : p * none = none := option.cases_on p rfl (λ _, rfl)

lemma defined_l [pmagma α] {p q : option α} : defined (p * q) → defined p :=
begin
  contrapose,
  assume (h0 : ¬ defined p),
  have e : p = none, from option.not_is_some_iff_eq_none.mp h0, 
  rw e,
  simp,
end

lemma defined_r [pmagma α] {p q : option α} : defined (p * q) → defined q :=
begin
  contrapose,
  assume (h0 : ¬ defined q),
  have e : q = none, from option.not_is_some_iff_eq_none.mp h0, 
  rw e,
  simp,
end

def tot [pmagma α] (a : α) : Prop := ∀ x : α, defined (↓a * ↓x) = tt

def pmagma.equiv [pmagma α] (a b : option α) : Prop := ∀ x : α, a * ↓x = b * ↓x
infix ` ≃ `:50 := pmagma.equiv

@[refl] lemma pmagma.refl [pmagma α] (a : option α) : a ≃ a := λ x, rfl

@[trans] lemma pmagma.trans [pmagma α] (a b c : option α) (eab : a ≃ b) (ebc : b ≃ c) : a ≃ c :=
by { intros x, rw (eab x), exact ebc x, }

/- Partial Combinatory Algebra -/
class pca (α : Type u) extends pmagma α :=
(k : α)
(k_constant : ∀ x y : α, k ⬝ x * y = x)
(s : α)
(s_defined : ∀ x y : α, defined (s ⬝ x * y))
(s_substitution : ∀ x y z : α, s ⬝ x * y * z = (x ⬝ z) * (y ⬝ z))

namespace pca

variables [pca α]

lemma ktot : tot (k : α) :=
by { intros x, have h : defined (k ⬝ x * x) = tt, { rw k_constant x x, refl, }, exact defined_l h, }

lemma stot : tot (s : α) := λ a, defined_l (s_defined a a)

def const (x : α) : α := option.get (ktot x)
def subst (x y : α) : α := option.get (s_defined x y)
notation `𝐤` := const
notation `𝐬` := subst

@[simp] lemma k_simp (a : α) : ↓k * ↓a = ↓(𝐤 a) := by { simp [const], }
@[simp] lemma s_simp (a b : α) : ↓s * ↓a * ↓b = ↓(𝐬 a b) := by { simp [subst], refl }
@[simp] lemma k_simp0 (a b : α) : ↓(𝐤 a) * ↓b = ↓a := by { rw ← k_simp, exact k_constant _ _, }
@[simp] lemma s_simp0 (a b c : α) : ↓(𝐬 a b) * ↓c = (↓a * ↓c) * (↓b * ↓c) := by { rw ← s_simp, exact s_substitution _ _ _, }

def i : α := 𝐬 k k
@[simp] lemma i_ident (a : α) : ↓i * ↓a = ↓a := by { simp [i], }
lemma itot : tot (i : α) := by { intros x, simp, refl, }

def subst' (x : α) : α := option.get (stot x)
notation `𝐬'` := subst'

class nontotal (α : Type u) [pmagma α] :=
(div0 div1 : α)
(nontot : div0 ⬝ div1 = none)

namespace nontotal

@[simp] lemma nontototal_simp [pmagma α] [nontotal α] : (↓div0 * ↓div1 : option α) = none := nontot

def divergent [nontotal α] : α := 𝐬 (𝐤 div0) (𝐤 div1)
theorem divergent_udefined [nontotal α] (a : α) : udefined (↓divergent * ↓a) = tt := by { simp[divergent], refl, }

theorem k_ne_s [nontotal α] : (k : α) ≠ s :=
begin
  assume e : k = s,
  have e0 : ↓(i : α) = ↓divergent,
  { calc
      ↓(i : α) = ↓k * (↓k * ↓i) * (↓k * ↓divergent) * ↓divergent : by { simp, }
      ...      = ↓s * (↓k * ↓i) * (↓k * ↓divergent) * ↓divergent : by { rw e, }
      ...      = ↓divergent                                      : by { simp, }, },
  have c  : defined (↓(i : α) * ↓k) = tt, { simp, refl, },
  have c0 : defined (↓(i : α) * ↓k) = ff, { rw e0, simp[divergent], },
  show false, from bool_iff_false.mpr c0 c,
end

instance [nontotal α] : nontrivial α := ⟨⟨k, s, k_ne_s⟩⟩

end nontotal

class extentional_in (A : set α) [pmagma α]
(ext : ∀ x y, x ∈ A → y ∈ A → defined (↓x * ↓y))

end pca
