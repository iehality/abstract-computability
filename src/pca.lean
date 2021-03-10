import data.option.basic

universe variable u

class partial_magma (α : Type u) :=
(mul : α → α → option α)

@[simp]
def partial_magma.mmul {α : Type u} [partial_magma α] : option α → option α → option α
| (some x) (some y) := partial_magma.mul x y
| none _ := none
| _ none := none
infixl ` ⬝ ` := partial_magma.mul

infix ` ↓= `:50 := λ x y, x = some y

instance pm_mul {α : Type u} [c : partial_magma α] : has_mul (option α) := {mul := @partial_magma.mmul _ c}
instance a_to_option_a {α : Type u} : has_coe α (option α) := ⟨some⟩

/- Partial Computability Algebla -/
class pca (α : Type u) extends partial_magma α :=
(k : α)
(ktot : ∀ x, option.is_some (k ⬝ x))
(hk : ∀ x y, k ⬝ x * (some y) = some x)
(s : α)
(stot : ∀ x y : α, option.is_some (s ⬝ x * y))
(hs : ∀ x y z : α, s ⬝ x * y * z = (x ⬝ z) * (y ⬝ z))

namespace pca

variables {α : Type u}

@[simp] lemma kh_ [c : pca α] : ∀ x y : α, k ⬝ x * (some y) = some x := c.hk
@[simp] lemma sh_ [c : pca α] : ∀ x y z : α, s ⬝ x * (some y) * (some z) = (x ⬝ z) * (y ⬝ z) := c.hs

def i' [pca α] : option α := s ⬝ k * (some k)

lemma i'_defined [pca α] : option.is_some (i' : option α) = tt := stot k k

def i [pca α] : α := option.get i'_defined

@[simp]
lemma i'_ident [pca α] (x : α) : i' * (some x) ↓= x := 
by { calc
    i' * some x = k ⬝ x * k ⬝ x                        : by { unfold i', simp }
    ...         = k ⬝ x * (some (option.get (ktot x))) : by { simp }
    ...         = some x                               : by { simp only [kh_] } }

@[simp]
lemma i_ident [pca α] (x : α) : i ⬝ x ↓= x :=
begin
  have e : i' = some i, { unfold i, simp },
  calc
    i ⬝ x = i' * (some x) : by { rw e, exact rfl }
    ...   = some x        : by { exact i'_ident _ },
end


inductive lambda
| var : ℕ → lambda
| K : lambda
| S : lambda
| I : lambda
| app : lambda → lambda → lambda

open lambda

local infixl ` *ₗ `:60 := app

def lam : ℕ → lambda → lambda
| x (var y) := if x = y then I else K *ₗ var y
| x K := K *ₗ K
| x S := K *ₗ S
| x I := K *ₗ I
| x (l *ₗ k) := S *ₗ (lam x l) *ₗ (lam x k)
notation `Λ`x`,` := lam x 

#check @lam

#check Λ 0, K *ₗ (var 0)

def l_to_pca [pca α] : lambda → option α
| (var x) := some k
| K := some k
| S := some s
| I := some i
| (l *ₗ k) := (l_to_pca l) * (l_to_pca k)

instance lambda_to_pca {α : Type u} [pca α] : has_coe lambda (option α) := ⟨l_to_pca⟩ 

#check congr_arg coe

lemma mmul_some_some [pca α] (x y : α) : (some x) * (some y) = x ⬝ y := rfl

lemma lambda_defined [pca α] : ∀ (e : lambda) (n : ℕ) , option.is_some (l_to_pca (Λ n, e) : option α) :=
begin
  intros e n,
  induction e,
  { cases (eq.decidable n e),
    { have he : Λ n, (var e) = K *ₗ var e, { simp [lam], intros, contradiction },
      rw he,
      exact ktot _,  },
    { have he : Λ n, (var e) = I, { simp [lam], intros, contradiction },
      rw he,
      exact rfl } },
  { exact ktot _ },
  { exact ktot _ },
  { exact ktot _ },
  { simp [lam, l_to_pca], 
    let a := option.get e_ih_ᾰ,
    let b := option.get e_ih_ᾰ_1,
    have ha : l_to_pca (Λ n, e_ᾰ) = some a, { simp },
    have hb : l_to_pca (Λ n, e_ᾰ_1) = some b, { simp },
    rw [ha, hb],
    exact stot _ _ }
end

end pca

