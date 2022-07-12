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

--todo: Cayley graph is preconnected

theorem cayley_connected (G: Type*) [group G] (S : set G)
 (hS : G = subgroup.closure S) : (cayley_graph G S hS).preconnected :=
begin
intros x y,
sorry
end

noncomputable instance word_metric {G: Type} [group G] (S : set G) (hS : G = subgroup.closure S) : pseudo_metric_space G :=
{
to_has_dist := ⟨ λ g h : G, cayley_dist S hS g h ⟩,
dist_self := begin
intro x, 
dsimp,
unfold cayley_dist,
apply (simple_graph.reachable.dist_eq_zero_iff ((cayley_connected G S hS) x x)).mpr,
sorry
end,
dist_comm := begin
simp,
unfold cayley_dist,
apply @simple_graph.dist_comm _ (cayley_graph G S hS),
end,






}











end