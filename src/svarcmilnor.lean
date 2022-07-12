import .isomaction
import .quasiisometry
import .geodesicspace
import .cayleygraphs
import tactic
import data.real.basic 
import topology.metric_space.isometry

import algebra.big_operators

open_locale big_operators 

open classical

lemma sum_le_prod (n:ℕ) (x: ℕ → ℝ) (l:ℝ)
  (h: ∀ i, x i ≤ l) : ∑i in finset.range (n+1), x i ≤ ((n+1):ℝ)*l := 
begin
  induction n with d hd,
    {dsimp,
    rw finset.sum_singleton,
    have g : x 0 ≤ l,
      {exact h 0, },
    simp [h],},
    {
      rw [finset.sum_range_succ, add_mul], 
      apply add_le_add,
      simp,
      exact hd,
      simp [h d.succ],
    }
end

theorem metric_svarcmilnor1 {α : Type*} {β : Type*} [group α] (c : ℝ) (b : ℝ) [quasigeodesic_space β c b] 
  [isom_action α β] (s : set β) (htrans: @translates_cover α β _ _ _ s) (finitediam : metric.bounded s)
   : α = subgroup.closure (@proper_action_set α _ _ _ _ s) := sorry

theorem metric_svarcmilnor2 {α : Type*} {β : Type*} [group α] (c : ℝ) (b : ℝ) [quasigeodesic_space β c b] 
  [isom_action α β] (s : set β) (htrans: @translates_cover α β _ _ _ s) (finitediam : metric.bounded s)
   : ∀ x : β, @is_QI α β (word_metric (@proper_action_set α _ _ _ _ s) (metric_svarcmilnor1 c b s htrans finitediam)) _ (λ g : α, g • x) := sorry


