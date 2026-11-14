module

public import Oberwolfach.OrderedOrdinaryPairBound

@[expose] public section
/-! Pair loads needed when a later retention changes spoke resources.
A different hub contributes zero; a spoke disjoint from the root rim
fixes three rim vertices and one hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

theorem ordered_ordinary_spokes_different_hubs_zero
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (v x:V) (u t:U) (hut:u≠t):
    resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inr (v,u)) (Sum.inr (x,t))=0 := by
  unfold resourceOmittedPairWeight
  apply Finset.sum_eq_zero
  intro W _
  split_ifs with h
  · have h₁:W.2=u := (orderedOrdinary_spoke_endpoint W v u h.1).2
    have h₂:W.2=t := (orderedOrdinary_spoke_endpoint W x t h.2.1).2
    exact (hut (h₁.symm.trans h₂)).elim
  · rfl

theorem ordered_ordinary_spoke_rim_three_vertices
    (hm:2≤m) (hn:0<Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (v x y:V) (u:U) (hvx:v≠x) (hvy:v≠y):
    resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inr (v,u)) (Sum.inl (x,y))≤
      ((m:ℝ)+1)^3*B/(Fintype.card V:ℝ)^2 := by
  let P:=fun W:OrderedOrdinaryWheel (U:=U) π b (m+1)=>
    Sum.inr (v,u)∈orderedOrdinaryResources W ∧ Sum.inl (x,y)∈orderedOrdinaryResources W
  have heq:resourceOmittedPairWeight orderedOrdinaryResources w (Sum.inr (v,u)) (Sum.inl (x,y))=
      ∑ W,if P W then w W else 0:=by
    unfold resourceOmittedPairWeight
    apply Finset.sum_congr rfl
    intro W _
    simp [P]
  rw [heq]
  by_cases hex:∃W,P W
  · obtain ⟨W,hW⟩:=hex
    have hxy:x≠y:=(orderedOrdinary_rim_endpoints W (by omega) x y hW.2).1
    have hc:({v,x,y}:Finset V).card=3:=by simp [hvx,hvy,hxy]
    have hh:=orderedOrdinary_fixed_hub_event hn w B hB (fun W=>(hw W).2)
      {v,x,y} (by omega) (by omega) u P (by
        intro Z hZ
        have h1:=orderedOrdinary_spoke_endpoint Z v u hZ.1
        have h2:=orderedOrdinary_rim_endpoints Z (by omega) x y hZ.2
        refine ⟨?_,h1.2⟩
        intro z hz
        simp only [Finset.mem_insert,Finset.mem_singleton] at hz
        rcases hz with rfl|rfl|rfl
        · exact h1.1
        · exact h2.2.1
        · exact h2.2.2)
    simp only [hc,show 3-1=2 from rfl] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro Z _
    split_ifs <;> rfl
  · have hf:∀W,¬P W:=by simpa using hex
    simp only [hf,ite_false,Finset.sum_const_zero]
    positivity
end Oberwolfach
