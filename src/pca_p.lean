
universe variable u

class partial_magma (α : Type u) extends has_mul α :=
(convergent : α → α → Prop)

instance pm_mul {M : Type u} {pm : partial_magma M} : has_mul M := {mul := pm.mul}

/- Partial Computability Algebla -/
class pca (α : Type u) extends has_mul α :=
(undefined : α)
(undefl : ∀ x, undefined * x = undefined)
(k : α)
(kdef : k ≠ undefined)
(ktot : ∀ x y, k * x * y = x)
(s : α)
(stot : ∀ x y, s * x * y = undefined → x = undefined ∨ y = undefined)
(hs : ∀ x y z, s * x * y * z = (x * z) * (y * z))

namespace pca
variables {α : Type u}
variables A : pca α

def convergent [pca α] (a : α) : Prop := (a ≠ pca.undefined)

def total [pca α] (a : α) : Prop := ∀ x, a * x = undefined → x = undefined

#check pca.total

lemma K_total [c : pca α] : @total _ c k :=
by { intros x h, rw ← (hk x k), rw h, exact undefl _ }

def pca.equiv [pca α] (a b : α) : Prop := ∀ x, a * x = b * x
infix ` ≃ `:50 := pca.equiv 

lemma eqiv_symm [pca α] (a b : α) : a ≃ b → b ≃ a :=
by { assume h x, rw (h x) }

infix ` ↓= ` :50 := λ a b, convergent a ∧ a = b
variables a b c : α
#check convergent

inductive accessible [pca α] : α → Prop
| k : accessible k
| s : accessible s
| app {a b} : accessible a → accessible b → accessible (a * b)

def partial_computable [pca α] (a : α) : Prop := convergent a ∧ accessible a
def computable [pca α] (a : α) : Prop := partial_computable a ∧ total a

@[simp] lemma hk_ [pca α] : ∀ (x y : α), k * x * y = x := λ x y, pca.hk x y
@[simp] lemma hs_ [pca α] : ∀ (x y z : α), s * x * y * z = (x * z) * (y * z) := λ x y z, pca.hs x y z

def I {α : Type u} [pca α] : α := s * k * k

@[simp] lemma I_identity [pca α] : ∀ x :α, I * x = x := by { intros, unfold I, simp }

inductive lambda (α : Type u)
| var : ℕ → lambda
| trm : α → lambda
| app : lambda → lambda → lambda

open lambda

local infixl ` ⬝ ` := app

def lam [pca α] : ℕ → lambda α → lambda α
| x (var y) := if x = y then trm I else trm k ⬝ var y
| x (trm c) := trm k ⬝ trm c
| x (app l k) := trm s ⬝ (lam x l) ⬝ (lam x k)
notation `Λ`x`,` := lam x 

def lambda_to_pca [pca α] : lambda α → α
| (var x) := k
| (trm a) := a
| (l ⬝ k) := (lambda_to_pca l) * (lambda_to_pca k)


