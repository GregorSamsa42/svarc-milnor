/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.txt.
Author: Georgi Kocharyan.
-/

import tactic
import data.real.basic 
import topology.metric_space.isometry
import topology.metric_space.emetric_space
import data.set.finite
import algebra.big_operators

open_locale big_operators 

open classical
open metric

@[class]
structure isom_action  (α : Type*) (β : Type*) [monoid α] [pseudo_metric_space β] extends mul_action α β :=
(isom : ∀ g : α, isometry (λ x : β , g•x))

/-instance (α : Type*) (β : Type*) [monoid α] [metric_space β] 
  : has_coe (isom_action α β) (mul_action α β)
:= ⟨isom_action.to_mul_action⟩ 
-/
open metric

lemma isom_of_isom_action {α : Type*} {β : Type*} [monoid α] [pseudo_metric_space β] 
[isom_action α β] :
∀ g : α, isometry (λ x : β , g•x)
:= isom_action.isom

lemma dist_of_isom {α : Type*} {β : Type*} [monoid α] [pseudo_metric_space β] 
[isom_action α β] (g : α) (x y : β) : dist x y = dist (g • x) (g • y) :=
begin
  apply eq.symm,
  apply isometry.dist_eq,
  exact isom_of_isom_action g,
end

lemma dist_of_inv_isom (α : Type*) (β : Type*) [group α] [pseudo_metric_space β] 
[isom_action α β] (g h : α) (x y : β) : dist (g • x) (h • y) = dist (x) ((g⁻¹*h) • y) :=
begin
  have k : dist (g • x) (h • y) = dist ((g⁻¹*g) • x) ((g⁻¹ * h) • y),
  repeat {rw ← smul_smul,},
  rw ← dist_of_isom (g⁻¹),
  rw k,
  simp,
  rw smul_smul,
end

def isom_img {α : Type*} {β : Type*} [monoid α] [pseudo_metric_space β] 
[isom_action α β] (g : α) (s : set β) :=
(λ x : β , g•x) '' s
--{x : β | ∃ y : β, y ∈ s ∧ g•y = x}

-- das hätte ich gerne mit • notation

theorem isom_img_inv {α : Type*} {β : Type*} [group α] [pseudo_metric_space β] 
[isom_action α β] (g : α) (s : set β) (x : β) (hx : x ∈ isom_img g s ) : g⁻¹ • x ∈ s :=
begin
rcases hx with ⟨ z, ⟨ zs, hz⟩ ⟩, dsimp at hz,
rw ← hz,
simp,
exact zs,
end

theorem isom_img_self {α : Type*} {β : Type*} [group α] [pseudo_metric_space β] 
[isom_action α β] (g : α) (s : set β) {x : β} (hx : x ∈ s) : g • x ∈ isom_img g s :=
begin
use x,
split,
exact hx,
simp,
end


theorem isom_img_one {α : Type*} {β : Type*} [group α] [pseudo_metric_space β] 
[isom_action α β] (s : set β) : s = isom_img (1:α) s :=
begin
apply subset_antisymm,
intros x hx,
use x,
split,
exact hx,
simp,
intros y hy,
rcases hy with ⟨z, ⟨hz1, hz2 ⟩⟩,
dsimp at hz2,
rw ← hz2,simp,
exact hz1,
end

theorem isom_img_mul {α : Type*} {β : Type*} [group α] [pseudo_metric_space β] 
[isom_action α β] (g: α) (s : set β) (x : β) (hx : x ∈ isom_img g s ) (h : α): h • x ∈ isom_img (h*g) s  :=
begin
rcases hx with ⟨ z, ⟨ zs, hz⟩ ⟩, dsimp at hz,
rw ← hz,
use z,
split, 
exact zs,
dsimp,
rw smul_smul,
end

lemma diam_preserved {α : Type*} {β : Type*} [monoid α] [pseudo_metric_space β] 
[isom_action α β] (s : set β) (g : α) : diam (isom_img g s) = diam s :=
begin
rw isom_img,
apply isometry.diam_image,
exact isom_action.isom g,
end

 def set_closed_ball {α : Type*} [pseudo_metric_space α] (s : set α) (ε : ℝ):
set α :=
{y : α | ∃ x : α, x ∈ s ∧ dist y x ≤ ε}

lemma self_set_closed_ball {α : Type*} [pseudo_metric_space α] (s : set α) (ε : ℝ) (enonneg: ε ≥ 0) (x : α) :
x ∈ s → x ∈ set_closed_ball s ε :=
begin
intro xs,
use x,
split,
exact xs,
rw dist_self, exact enonneg,
end

theorem isom_of_set_closed_ball {α : Type*} {β : Type*} [group α] [pseudo_metric_space β] [isom_action α β]
 (s : set β) (g : α) (ε : ℝ): isom_img g (set_closed_ball s ε) = set_closed_ball (isom_img g s) ε :=
begin
apply subset_antisymm,
intros x hx, 
rw set_closed_ball,
dsimp,
rcases hx with ⟨y, ⟨⟨z, ⟨hz1, hz2⟩⟩, hy2⟩ ⟩,
use g • z,
split,
use z, split,
exact hz1,
dsimp, refl,
dsimp at hy2,
rw ← hy2,
rw ← dist_of_isom, exact hz2,
-- before here could have had α monoid
rintros x ⟨y, ⟨⟨ z, ⟨hz1, hz2⟩⟩, hy2⟩⟩,
rw isom_img,
use g⁻¹ • x, split,
rw set_closed_ball, dsimp,
use z, 
split, 
{ exact hz1, },
dsimp at hz2,
have inv: z = g⁻¹ • y,
  {rw ← hz2, rw ← smul_assoc, simp,},
rw inv,
rw ← dist_of_isom, exact hy2, dsimp,
rw smul_smul, 
simp,
end


theorem diam_of_ball_of_diam {α : Type*} [pseudo_metric_space α] (B : set α) (ε : ℝ) (epos: ε ≥ 0) : diam (set_closed_ball B ε ) ≤ 2*ε + diam B :=
begin
  apply diam_le_of_forall_dist_le,
  linarith [@diam_nonneg _ _ B],
  rintros x ⟨a, ⟨ha1, ha2 ⟩ ⟩ y ⟨b, ⟨hb1, hb2⟩ ⟩,
  calc
    dist x y ≤ dist x a + dist a y  : dist_triangle x a y
    ...      ≤ dist x a + dist a b + dist b y : begin rw add_assoc, apply add_le_add (le_refl (dist x a)) (dist_triangle a b y), end
    ...      = dist x a + dist b y + dist a b : by rw add_comm (dist a b) (dist b y)
    ...      ≤ ε + ε + dist a b : by sorry
    ...      ≤ 2*ε + diam B : by sorry
end


def proper_action_set (α : Type*) {β : Type*} [monoid α] [pseudo_metric_space β] 
  [isom_action α β] (s : set β) : set α := 
   {g : α | s ∩ (isom_img g s) ≠ ∅}

def translates_cover (α : Type*) {β : Type*} [monoid α] [pseudo_metric_space β] 
  [isom_action α β] (s : set β) : Prop :=
  ∀ x : β, x ∈ (⋃ g : α, isom_img g s)

theorem exists_cover_element {α : Type*} {β : Type*} [monoid α] [pseudo_metric_space β] 
  [isom_action α β] {s : set β} (h : translates_cover α s) (x : β) : ∃ g : α, x ∈ isom_img g s  :=
  begin
  have hx : x ∈ (⋃ g : α, isom_img g s),
    apply h,
  rw set.mem_Union at hx,
  cases hx with i hi,
  use i, exact hi,
  end

  noncomputable def cover_element {α : Type*} {β : Type*} [monoid α] [pseudo_metric_space β] 
  [isom_action α β] {s : set β} (h : translates_cover α s) (x : β) : α :=
  classical.some (exists_cover_element h x)



