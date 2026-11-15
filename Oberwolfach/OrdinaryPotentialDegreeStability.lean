module

public import Oberwolfach.OrdinaryPotentialChanges
public import Oberwolfach.RelationIncidentWeights

@[expose] public section

/-! Actual degree-controlled stability of all ordinary potential wheel loads.
The root can be absent, and coefficients remain fixed during the change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (P F : SimpleGraph V) (Hbase : V → U → Prop) (r : ℕ)
    (hr : 2≤r) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : OrdinaryWheel P F Hbase r → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
    (Q Q' : SimpleGraph V) (H H' : V → U → Prop) (d : ℝ) (hd : 0≤d)
    (hQ : ∀ x,(∑ y,bipAdj (fun x y=>¬(Q.Adj x y↔Q'.Adj x y)) x y)≤d)
    (hHout : ∀ x,(∑ u,bipAdj (fun x u=>¬(H x u↔H' x u)) x u)≤d)
    (hHin : ∀ u,(∑ x,bipAdj (fun x u=>¬(H x u↔H' x u)) x u)≤d)
include hr hn hu hB hw hd hQ hHout hHin

theorem ordinaryPotentialLoad_rim_degree_stability (x y : V) (hxy : x≠y) :
    |ordinaryPotentialLoad w (Sum.inl s(x,y)) Q' H'-ordinaryPotentialLoad w (Sum.inl s(x,y)) Q H|≤
      8*(r:ℝ)^4*B*d/Fintype.card V := by
  let Dq := fun x y=>¬(Q.Adj x y↔Q'.Adj x y)
  let Dh := fun x u=>¬(H x u↔H' x u)
  let n : ℝ := Fintype.card V
  let K : ℝ := (r:ℝ)^4*B
  let M := K/n
  let N := K/n^2
  have hn0 : 0<n := Nat.cast_pos.mpr hn
  have hM : 0≤M := by dsimp [M,K];positivity
  have hN : 0≤N := by dsimp [N,K];positivity
  have hQi (y : V) : (∑ x,bipAdj Dq x y)≤d := by
    have he : (∑ x,bipAdj Dq x y)=∑ x,bipAdj Dq y x := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [bipAdj,Dq,Q.adj_comm,Q'.adj_comm]
      all_goals split_ifs <;> rfl
    rw [he];exact hQ y
  have hR := relation_root_incident_cost Dq d hQ hQi {x,y} {x,y} M N hM hN
  have hS := relation_root_incident_cost Dh d hHout hHin {x,y} ∅ M N hM hN
  have hc : ({x,y}:Finset V).card=2 := by simp [hxy]
  simp only [hc,Nat.cast_ofNat,Finset.card_empty,Nat.cast_zero,Finset.notMem_empty,or_false,add_zero] at hR hS
  have hstart := ordinaryPotentialLoad_stability_ordered w (fun W=>(hw W).1) (Sum.inl s(x,y)) Q Q' H H'
  apply hstart.trans
  calc
    _ ≤ (∑ z,∑ t,if Dq z t then (if z∈({x,y}:Finset V) ∨ t∈({x,y}:Finset V) then M else N) else 0)+
        (∑ z,∑ u,if Dh z u then (if z∈({x,y}:Finset V) then M else N) else 0) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro z _
        apply Finset.sum_le_sum
        intro t _
        by_cases h : Dq z t
        · dsimp only [Dq,Dh] at h ⊢
          simp only [h,ite_true,ite_false]
          apply ordinaryOmittedPairLoad_rim_cost P F Hbase r hr hn hu w B hB hw x y z t hxy
        · dsimp only [Dq,Dh] at h ⊢
          simp only [h,ite_true,ite_false,le_refl]
      · apply Finset.sum_le_sum
        intro z _
        apply Finset.sum_le_sum
        intro u _
        by_cases h : Dh z u
        · dsimp only [Dq,Dh] at h ⊢
          simp only [h,ite_true,ite_false]
          apply ordinaryOmittedPairLoad_rim_spoke_cost P F Hbase r hr hn hu w B hB hw x y z u hxy
        · dsimp only [Dq,Dh] at h ⊢
          simp only [h,ite_true,ite_false,le_refl]
    _ ≤ d*((2+2)*M+n*N)+d*(2*M+n*N) := by
      convert (add_le_add hR hS) using 1
      all_goals congr 1 <;> (apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; split_ifs <;> rfl)
    _ = _ := by dsimp only [M,N,K,n];field_simp;ring

theorem ordinaryPotentialLoad_spoke_degree_stability (v : V) (u : U) :
    |ordinaryPotentialLoad w (Sum.inr (v,u)) Q' H'-ordinaryPotentialLoad w (Sum.inr (v,u)) Q H|≤
      4*(r:ℝ)^4*B*d/Fintype.card V := by
  let Dq := fun x y=>¬(Q.Adj x y↔Q'.Adj x y)
  let Dh := fun x u=>¬(H x u↔H' x u)
  let n : ℝ := Fintype.card V
  let K : ℝ := (r:ℝ)^4*B
  let M := K/n
  let N := K/n^2
  have hn0 : 0<n := Nat.cast_pos.mpr hn
  have hM : 0≤M := by dsimp [M,K];positivity
  have hN : 0≤N := by dsimp [N,K];positivity
  have hQi (y : V) : (∑ x,bipAdj Dq x y)≤d := by
    have he : (∑ x,bipAdj Dq x y)=∑ x,bipAdj Dq y x := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [bipAdj,Dq,Q.adj_comm,Q'.adj_comm]
      all_goals split_ifs <;> rfl
    rw [he];exact hQ y
  have hR := relation_root_incident_cost Dq d hQ hQi {v} {v} M N hM hN
  have hS := relation_root_incident_cost Dh d hHout hHin ∅ {u} M 0 hM (by norm_num)
  simp only [Finset.card_singleton,Nat.cast_one,Finset.mem_singleton] at hR
  simp only [Finset.card_empty,Nat.cast_zero,Finset.card_singleton,Nat.cast_one,
    Finset.notMem_empty,Finset.mem_singleton,false_or,zero_add,mul_zero,add_zero,one_mul] at hS
  have hstart := ordinaryPotentialLoad_stability_ordered w (fun W=>(hw W).1) (Sum.inr (v,u)) Q Q' H H'
  apply hstart.trans
  calc
    _ ≤ (∑ x,∑ y,if Dq x y then (if x=v ∨ y=v then M else N) else 0)+
        (∑ x,∑ t,if Dh x t then (if t=u then M else 0) else 0) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        by_cases h : Dq x y
        · dsimp only [Dq,Dh] at h ⊢
          simp only [h,ite_true,ite_false]
          apply ordinaryOmittedPairLoad_spoke_rim_cost P F Hbase r hr hn hu w B hB hw v x y u
        · dsimp only [Dq,Dh] at h ⊢
          simp only [h,ite_true,ite_false,le_refl]
      · apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro t _
        by_cases h : Dh x t
        · dsimp only [Dq,Dh] at h ⊢
          simp only [h,ite_true,ite_false]
          apply ordinaryOmittedPairLoad_spokes_cost P F Hbase r hr hn hu w B hB hw v x u t
        · dsimp only [Dq,Dh] at h ⊢
          simp only [h,ite_true,ite_false,le_refl]
    _ ≤ d*((1+1)*M+n*N)+d*M := by
      convert (add_le_add hR hS) using 1
      all_goals congr 1 <;> (apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; split_ifs <;> rfl)
    _ = _ := by dsimp only [M,N,K,n];field_simp;ring

end Oberwolfach
