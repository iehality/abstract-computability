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

/- Partial Combinatory Algebra -/
class pca (α : Type u) extends partial_magma α :=
(k : α)
(ktot : ∀ x, option.is_some (k ⬝ x))
(k_constant : ∀ x y : α, k ⬝ x * y = x)
(s : α)
(stot : ∀ x y : α, option.is_some (s ⬝ x * y))
(s_substitution : ∀ x y z : α, s ⬝ x * y * z = (x ⬝ z) * (y ⬝ z))

def pca.equiv {α : Type u} [partial_magma α] (a b : option α) : Prop := ∀ x, a * x = b * x
infix ` ≃ `:50 := pca.equiv 

namespace pca

variables {α : Type u}

@[simp] lemma k_constant_ [c : pca α] : ∀ x y : α, k ⬝ x * (some y) = some x := c.k_constant
@[simp] lemma s_substitution_ [c : pca α] : ∀ x y z : α, s ⬝ x * (some y) * (some z) = (x ⬝ z) * (y ⬝ z) := c.s_substitution

def i [pca α] : α := option.get (stot k k)

@[simp]
lemma i_ident [pca α] (x : α) : i ⬝ x ↓= x :=
begin
  have e : s ⬝ k * (some k) = some i, { unfold i, simp, refl },
  calc
    i ⬝ x = (s ⬝ k * (some k)) * (some x)        : by { rw e, exact rfl }
    ...   = k ⬝ x * k ⬝ x                        : by { simp }
    ...   = k ⬝ x * (some (option.get (ktot x))) : by { simp }
    ...   = some x                               : by { simp only [k_constant_] }
end

inductive lambda (α : Type u) [pca α]
| var : ℕ → lambda
| com : α → lambda
| app : lambda → lambda → lambda
instance lambda_mul (α : Type u) [pca α] : has_mul (lambda α) := ⟨lambda.app⟩

open lambda

def lam [pca α] : ℕ → lambda α → lambda α
| x (var y) := if x = y then (com i) else (com k) * var y
| x (com c) := com k * com c
| x (l * k) := com s * (lam x l) * (lam x k)
notation `Λ`x`,` := lam x 

def l_to_pca [pca α] : lambda α → option α
| (var x) := some k
| (com c) := some c
| (l * k) := (l_to_pca l) * (l_to_pca k)

instance lambda_to_pca {α : Type u} [pca α] : has_coe (lambda α) (option α) := ⟨l_to_pca⟩ 

lemma lambda_defined [c : pca α] : ∀ (n : ℕ) (e : lambda α), option.is_some (l_to_pca (Λ n, e) : option α)
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
    simp [lam, l_to_pca], 
    let a := option.get (lambda_defined n l),
    let b := option.get (lambda_defined n m),
    have ha : l_to_pca (Λ n, l) = some a, { simp },
    have hb : l_to_pca (Λ n, m) = some b, { simp },
    rw [ha, hb],
    exact stot a b
  end 

def dapp [pca α] : lambda α := Λ 0, (Λ 1, (Λ 2, (var 0) * ((var 1) * (var 1)) * (var 2)))


def fixpoint [pca α] : α := option.get (lambda_defined 0 (dapp * (var 0) *(dapp * (var 0))))
def fixpoint' [pca α] : option α := l_to_pca (Λ 0, dapp * (var 0) *(dapp * (var 0)))

theorem kleene_fixpoint [c : pca α] (f : α) :
  fixpoint ⬝ f ≃ f * (fixpoint ⬝ f) :=
begin
  have e : l_to_pca (Λ 0, (dapp * (var 0) * (dapp * (var 0)))) = some (@fixpoint _ c),
  { unfold fixpoint, simp },
  intros x,
  calc
    fixpoint ⬝ f * x = (l_to_pca (Λ 0, (dapp * (var 0) * (dapp * (var 0))))) * (some f) * x : by { rw e, exact rfl }
    ...              = (l_to_pca (dapp * (com f) * (dapp * (com f)))) * x : by { simp [lam, l_to_pca],  }
    ...              = f * fixpoint ⬝ f * x : by sorry
end


end pca

