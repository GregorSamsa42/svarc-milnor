/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Georgi Kocharyan.
-/

import group_theory.subgroup.basic
import tactic
import data.real.basic 
import topology.metric_space.isometry
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.metric
import group_theory.finiteness


variables {G : Type*} [group G] (S: set G) (hS: G = subgroup.closure S)


def cayley_relation (G: Type*) [group G] (S : set G) (hS : G = subgroup.closure S) : G → G → Prop :=
(λ g, (λ h, ∃ s : S, g*s = h))

def cayley_graph (G: Type*) [group G] (S : set G) (hS : G = subgroup.closure S) : simple_graph G :=
simple_graph.from_rel (cayley_relation G S hS)

noncomputable def cayley_dist {G : Type*} [group G] (S: set G) (hS: G = subgroup.closure S)
 (g : G) (h : G) : ℝ :=
(cayley_graph G S hS).dist g h

-- -- can probably not mention infinite lists
-- #check subgroup.list_prod_mem


-- theorem mem_closure_iff_finite_prod {G : Type*} [group G]
--  (S: set G) : ∀ x : G, (x ∈ subgroup.closure S ↔ ∃ l : list G, ((∀ x : G, x ∈ l → (x ∈ S ∨ x⁻¹ ∈ S) → list.prod l = x))):=
-- sorry

theorem generates_iff_subset {G: Type*} [group G] (S : set G) : G = subgroup.closure S ↔ ∀ x : G, x ∈ subgroup.closure S :=
begin
split,
intros hG x,
sorry,
end


theorem cayley_preconnected (G: Type*) [group G] (S : set G)
 (hS : G = subgroup.closure S) : (cayley_graph G S hS).preconnected :=
begin
intros x y, 
sorry,
end

theorem cayley_connected (G: Type*) [group G] [inhabited G] (S : set G)
 (hS : G = subgroup.closure S) : (cayley_graph G S hS).connected :=
begin
sorry,
end

noncomputable instance word_metric {G: Type*} [group G] [inhabited G] (S : set G)
 (hS : G = subgroup.closure S) : pseudo_metric_space G :=
{
  to_has_dist := ⟨ λ g h : G, cayley_dist S hS g h ⟩,
  dist_self := 
  begin
    intro x, 
    dsimp,
    unfold cayley_dist,
    simp,
  end,
  dist_comm := 
  begin
    simp,
    unfold cayley_dist,
    simp,
    intros x y,
    apply @simple_graph.dist_comm _ (cayley_graph G S hS),
  end,
dist_triangle := begin
simp,
unfold cayley_dist,
intros x y z,
-- simp [coe, lift_t], 
norm_cast,
apply @simple_graph.connected.dist_triangle _ (cayley_graph G S hS) (cayley_connected G S hS) x y z,
end
}

lemma adj_cayley {G: Type*} [group G] [pseudo_metric_space G] (S : set G) (hS : G = subgroup.closure S)
  (g : G) (h : G) :
dist g h = 1 ↔ ∃ (s ∈ S), h*s = g :=
begin
split,
intro d,
sorry,
end

lemma dist_of_mul {G: Type*} [group G] [pseudo_metric_space G] (S : set G) (hS : G = subgroup.closure S)
  (g : G) (h : G) (a : G) : dist g h = dist (a*g)(a*h) :=
  sorry

lemma dist_of_inv {G: Type*} [group G] [pseudo_metric_space G] (S : set G) (hS : G = subgroup.closure S)
  (g : G) (h : G) : dist g h = dist 1 (g⁻¹*h) :=
  sorry

lemma trunc_path {G: Type*} [group G] [pseudo_metric_space G] (S : set G) (hS : G = subgroup.closure S) (g : G) :
∃ (h : G) (s ∈ S), h*s = g ∧ dist 1 h = (dist 1 g) - 1 :=
begin
sorry,
end










end