import tactic
import data.real.basic 
import topology.metric_space.isometry

import algebra.big_operators

open_locale big_operators 

open classical

@[class]
structure isom_action  (α : Type*) (β : Type*) [monoid α] [metric_space β] extends mul_action α β :=
(isom : ∀ g : α, isometry (λ x : β , g•x))

/-instance (α : Type*) (β : Type*) [monoid α] [metric_space β] 
  : has_coe (isom_action α β) (mul_action α β)
:= ⟨isom_action.to_mul_action⟩ 
-/


lemma isom_of_isom_action {α : Type*} {β : Type*} [monoid α] [metric_space β] 
[isom_action α β] :
∀ g : α, isometry (λ x : β , g•x)
:= isom_action.isom

lemma dist_of_isom (α : Type*) (β : Type*) [monoid α] [metric_space β] 
[isom_action α β] : ∀ g : α, ∀ x y : β, dist x y = dist (g • x) (g • y) :=
begin
  intros g x y,
  apply eq.symm,
  apply isometry.dist_eq,
  exact isom_of_isom_action g,
end


example (n:ℕ) (x: finset.range n → ℝ) (l:ℝ)
  (h: ∀ i, x i ≤ l)
  : ∑i in range n, x i ≤ n*l 
:= by library_search 