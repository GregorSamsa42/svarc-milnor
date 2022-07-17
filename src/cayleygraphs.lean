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

-- can probably not mention infinite lists
#check subgroup.list_prod_mem


theorem mem_closure_iff_finite_prod {G : Type*} [group G]
 (S: set G) : ∀ x : G, (x ∈ subgroup.closure S ↔ ∃ l : list G, ((∀ x : G, x ∈ l → (x ∈ S ∨ x⁻¹ ∈ S) → list.prod l = x))):=
sorry

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
-- have 
sorry,
end


noncomputable instance word_metric {G: Type} [group G] (S : set G)
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
simp [coe, lift_t], 
 -- apply @simple_graph.connected.dist_triangle _ (cayley_graph G S hS),
sorry
end
}











end