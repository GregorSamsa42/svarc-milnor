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


variables {G : Type*} [group G] [inhabited G] (S: set G) (hS: G = subgroup.closure S)


def cayley_relation (S : set G) : G → G → Prop :=
(λ g, (λ h, ∃ s : S, g*s = h))

def cayley_graph (S : set G) : simple_graph G :=
simple_graph.from_rel (cayley_relation S )

noncomputable def cayley_dist (S: set G)
 (g : G) (h : G) : ℝ :=
(cayley_graph S).dist g h

-- -- can probably not mention infinite lists
-- #check subgroup.list_prod_mem


-- theorem mem_closure_iff_finite_prod {G : Type*} [group G]
--  (S: set G) : ∀ x : G, (x ∈ subgroup.closure S ↔ ∃ l : list G, ((∀ x : G, x ∈ l → (x ∈ S ∨ x⁻¹ ∈ S) → list.prod l = x))):=
-- sorry

theorem generates_iff_subset (S : set G) : G = subgroup.closure S ↔ ∀ x : G, x ∈ subgroup.closure S :=
begin
split,
intros hG x,
sorry,
end


theorem cayley_preconnected (S : set G)
 (hS : G = subgroup.closure S) : (cayley_graph S).preconnected :=
begin
intros x y, 
sorry,
end

theorem cayley_connected [inhabited G] (S : set G)
 (hS : G = subgroup.closure S) : (cayley_graph S).connected :=
begin
sorry,
end

noncomputable instance word_metric (S : set G)
 (hS : G = subgroup.closure S) : pseudo_metric_space G :=
{
  to_has_dist := ⟨ λ g h : G, cayley_dist S g h ⟩,
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
    apply @simple_graph.dist_comm _ (cayley_graph S ),
  end,
dist_triangle := 
  begin
    simp,
    unfold cayley_dist,
    intros x y z,
    norm_cast,
    apply @simple_graph.connected.dist_triangle _ (cayley_graph S) (cayley_connected S hS) x y z,
  end
}

noncomputable instance has_word_dist (S : set G)
 (hS : G = subgroup.closure S) : has_dist G :=
 (word_metric S hS).to_has_dist

variables (g: G)

-- def cay : pseudo_metric_space G := word_metric S hS
#check (word_metric S hS).dist g g
#check word_metric 
#check @dist

lemma adj_cayley {G: Type*} [group G]
  (g : G) (h : G) :
(word_metric S hS).dist g h = 1 ↔ ∃ (s ∈ S), h*s = g :=
begin
split,
intro d,
sorry,
end

lemma dist_of_mul {G: Type*} [group G]  
  (g : G) (h : G) (a : G) : dist g h = dist (a*g)(a*h) :=
  sorry

lemma dist_of_inv {G: Type*} [group G]
  (g : G) (h : G) : dist g h = dist 1 (g⁻¹*h) :=
  sorry

lemma trunc_path {G: Type*} [group G] (g : G) :
∃ (h : G) (s ∈ S), h*s = g ∧ dist 1 h = (dist 1 g) - 1 :=
begin
sorry,
end










end