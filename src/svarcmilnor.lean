import .isomaction
import .quasiisometry
import .geodesicspace
import .cayleygraphs
import tactic
import data.real.basic 
import topology.metric_space.isometry
import data.list.basic

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
      simp ,
      exact hd,
      simp [h d.succ],
    }
end

variables {α : Type*} {β : Type*} [inhabited β] [group α] [inhabited α]
-- L/nat.ceil(L/d)


lemma intS  (c : ℝ) (b : ℝ) (cpos: c > 0) (bnonneg: b ≥ 0)  [quasigeodesic_space β c b cpos bnonneg] 
  [isom_action α β] (s : set β) (finitediam : metric.bounded s) (g : α) (h : α) (x : β) (y : β) (hx: x ∈ isom_img g s)
  (hy : y ∈ isom_img h s) (hd : dist x y ≤ 2*b) 
  : ∃ t ∈ (@proper_action_set α _ _ _ _ (set_closed_ball s (2*b))), g*t = h
   := 
begin
use g⁻¹*h,
split,
have hy' : y ∈ set_closed_ball (isom_img g s) (2*b),
  {use x, split, exact hx, rw dist_comm, exact hd,},
rw ← isom_of_set_closed_ball at hy',
have hy'' : y ∈ isom_img h (set_closed_ball s (2*b)),
-- rcases hx with ⟨ z, ⟨ zs, hz ⟩⟩, dsimp at hz,
rcases hy with ⟨ w, ⟨ ws, hw ⟩⟩, dsimp at hw,
use w, 
split,
{ apply self_set_closed_ball, linarith, exact ws },
exact hw, rw proper_action_set, dsimp,
have i1 : g⁻¹ • y ∈ isom_img (g⁻¹ * g) (set_closed_ball s (2 * b)),
  { apply isom_img_mul, exact hy', },
simp at i1,
rw ← isom_img_one at i1,
have i2 : g⁻¹ • y ∈ isom_img (g⁻¹ * h) (set_closed_ball s (2 * b)),
  { apply isom_img_mul, exact hy'', },
apply set.nonempty.ne_empty,
rw set.nonempty_def,
use g⁻¹ • y,
exact ⟨i1, i2⟩,
exact g, exact x,
simp,
end

namespace list

theorem subdiv {L : ℝ} (Lnonneg : L ≥ 0) {d : ℝ} (dpos : d > 0)
 : ∃ l : list ℝ, l.head = 0 ∧ (l.reverse).head = L ∧ (∀ i : ℕ, (l.inth i)-(l.inth (i-1)) ≤ d ∧ l.inth i ≥ 0 ∧ l.inth i ≤ L) :=
begin
sorry
end

def right_inv_list (g : α) : list α → list α
| nil := [g]
| (cons a l) :=  (g* a⁻¹) :: ((a*(l.head)) :: (erasep (λ x, true) (right_inv_list l)))


lemma prod_of_inv (g : α) (l : list α) : g = list.prod (right_inv_list g l) :=
begin
sorry
end

theorem metric_svarcmilnor1  (c : ℝ) (b : ℝ) (cpos: c > 0) (bpos: b > 0)  [quasigeodesic_space β c b cpos (le_of_lt bpos)] 
  [isom_action α β] (s : set β) (htrans: translates_cover α s) (finitediam : metric.bounded s)
   : α = subgroup.closure (@proper_action_set α _ _ _ _ (set_closed_ball s (2*b))) :=
begin
rw generates_iff_subset,
intro g,
-- rw mem_closure_iff_finite_prod,
let x : β, exact default,
have h : conn_by_quasigeodesic' x (g • x) c b,
  apply quasigeodesic_space.quasigeodesics x (g • x),
rcases h with ⟨ L, Lpos, f, qif⟩,
have harch : ∃ n : ℕ, L ≤ (n : real)*b/c,
--apply real.archimedean.arch,
  {sorry},
cases harch with n hn,
induction n with d hd,



-- -- tlist is subdivision of [O,L] with distances smaller than b/c

-- have tplist : ∃ l : list ℝ, l.head = 0 ∧ (l.reverse).head = L ∧ (∀ i : ℕ, (l.inth i)-(l.inth (i-1)) ≤ b/c ∧  l.inth i ≥ 0 ∧ l.inth i ≤ L),
--   { apply subdiv Lpos (div_pos bpos cpos), },
-- rcases tplist with ⟨tlist, ⟨h1, ⟨h2,h3 ⟩⟩⟩,
-- have listint : ∀ r : ℝ, r ∈ tlist → (r ≥ 0 ∧ r ≤ L),
--   {sorry,},

-- -- xlist is images of tlist under quasigeodesic

-- let xlist := list.pmap (fpi L Lpos f) tlist listint,

-- -- glist are group elements so that g.s contains x

-- let glist := list.map (cover_element htrans) xlist,

end

theorem metric_svarcmilnor2 (c : ℝ) (b : ℝ) (cpos: c > 0) (bpos: b > 0)  [quasigeodesic_space β c b cpos (le_of_lt bpos)] 
  [isom_action α β] (s : set β) (htrans: @translates_cover α β _ _ _ s) (finitediam : metric.bounded s)
   : ∀ x : β, @is_QI α β (word_metric (@proper_action_set α _ _ _ _ (set_closed_ball s (2*b))) (metric_svarcmilnor1 c b s htrans finitediam)) _ (λ g : α, g • x) :=
   begin
   sorry
   end


