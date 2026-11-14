module

public import Oberwolfach.MarkedPotentialLoads
public import Oberwolfach.OccurrenceIncidentWeights

@[expose] public section

/-! Actual-degree stability for marked root-omitted wheel loads.
The parent wheel family, coefficients and permutation remain fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ : V → U → Prop}
  (hm : 3≤m) (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
  (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
  (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
  (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
  (R R' : E⊕K → Prop) (H H' : V → U → Prop) (d : ℝ) (hd : 0≤d)
  (hout : ∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim tail ktail e=x then (1:ℝ) else 0)≤d)
  (hin : ∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim head khead e=x then (1:ℝ) else 0)≤d)
  (hHout : ∀ x,(∑ u,bipAdj (fun x u=>¬(H x u↔H' x u)) x u)≤d)
  (hHin : ∀ u,(∑ x,bipAdj (fun x u=>¬(H x u↔H' x u)) x u)≤d)
include hm hp hn hu hB hw hd hout hin hHout hHin

theorem markedPotentialLoad_rim_degree_stability (e : E⊕K) :
    |markedPotentialLoad w R' H' (Sum.inl e)-markedPotentialLoad w R H (Sum.inl e)|≤
      8*((m:ℝ)+1)^4*B*d/Fintype.card V := by
  let n : ℝ := Fintype.card V
  let C : ℝ := ((m:ℝ)+1)^4*B
  let M : ℝ := C/n
  let N : ℝ := C/n^2
  let S : Finset V := {Sum.elim tail ktail e,Sum.elim head khead e}
  have hnR : 0<n := by dsimp [n]; exact_mod_cast hn
  have hM : 0≤M := by dsimp [M,C];positivity
  have hN : 0≤N := by dsimp [N,C];positivity
  have hS : (S.card : ℝ)≤2 := by
    have hh : S.card≤2 := by dsimp [S]; exact (Finset.card_insert_le _ _).trans (by simp)
    exact_mod_cast hh
  have hRcost := occurrence_root_incident_cost (Sum.elim tail ktail) (Sum.elim head khead)
    (fun e=>¬(R e↔R' e)) d (fun x=>by convert hout x using 1 <;> congr!) (fun x=>by convert hin x using 1 <;> congr!) S S M N hM hN
  have hHcost := relation_root_incident_cost (fun v u=>¬(H v u↔H' v u)) d hHout hHin S ∅ M N hM hN
  simp only [Finset.notMem_empty,or_false,Finset.card_empty,Nat.cast_zero,add_zero] at hHcost
  have hstart := markedPotentialLoad_change w (fun W=>(hw W).1) R R' H H' (Sum.inl e)
  apply hstart.trans
  calc
    _ ≤ (∑ f,if ¬(R f↔R' f) then (if Sum.elim tail ktail f∈S ∨ Sum.elim head khead f∈S then M else N) else 0)+
        (∑ v,∑ u,if ¬(H v u↔H' v u) then (if v∈S then M else N) else 0) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro f _
        by_cases hf : ¬(R f↔R' f)
        · rw [if_pos hf,if_pos hf,markedOmittedPair_rims]
          exact marked_rim_rim_pair_cost hm hp hn hu w B hB (fun W=>(hw W).2) e f
        · simp only [hf,ite_false,le_refl]
      · apply Finset.sum_le_sum
        intro v _
        apply Finset.sum_le_sum
        intro u _
        by_cases hf : ¬(H v u↔H' v u)
        · rw [if_pos hf,if_pos hf,markedOmittedPair_rim_spoke]
          exact marked_rim_spoke_pair_cost hm hp hn w B hB (fun W=>(hw W).2) e v u
        · simp only [hf,ite_false,le_refl]
    _ ≤ d*(6*M+2*n*N) := by
      calc
        _ ≤ d*((S.card+S.card:ℝ)*M+(Fintype.card V:ℝ)*N)+d*((S.card:ℝ)*M+(Fintype.card V:ℝ)*N) := by
          convert add_le_add hRcost hHcost using 1 <;> congr!
        _ ≤ _ := by
          have hs := mul_le_mul_of_nonneg_right hS hM
          have hs' := mul_le_mul_of_nonneg_left hs hd
          dsimp only [n]
          nlinarith only [hs']
    _ = _ := by dsimp [M,N,C,n];field_simp;ring

theorem markedPotentialLoad_spoke_degree_stability (v : V) (u : U) :
    |markedPotentialLoad w R' H' (Sum.inr (v,u))-markedPotentialLoad w R H (Sum.inr (v,u))|≤
      4*((m:ℝ)+1)^4*B*d/Fintype.card V := by
  let n : ℝ := Fintype.card V
  let C : ℝ := ((m:ℝ)+1)^4*B
  let M : ℝ := C/n
  let N : ℝ := C/n^2
  have hnR : 0<n := by dsimp [n]; exact_mod_cast hn
  have hM : 0≤M := by dsimp [M,C];positivity
  have hN : 0≤N := by dsimp [N,C];positivity
  have hRcost := occurrence_root_incident_cost (Sum.elim tail ktail) (Sum.elim head khead)
    (fun e=>¬(R e↔R' e)) d (fun x=>by convert hout x using 1 <;> congr!) (fun x=>by convert hin x using 1 <;> congr!) {v} {v} M N hM hN
  have hHcost := relation_root_incident_cost (fun v u=>¬(H v u↔H' v u)) d hHout hHin ∅ {u} M 0 hM (by norm_num)
  simp only [Finset.card_singleton,Nat.cast_one,Finset.mem_singleton] at hRcost
  simp only [Finset.card_empty,Nat.cast_zero,Finset.card_singleton,Nat.cast_one,
    Finset.notMem_empty,Finset.mem_singleton,false_or,zero_add,mul_zero,add_zero,one_mul] at hHcost
  have hstart := markedPotentialLoad_change w (fun W=>(hw W).1) R R' H H' (Sum.inr (v,u))
  apply hstart.trans
  calc
    _ ≤ (∑ e,if ¬(R e↔R' e) then (if Sum.elim tail ktail e=v ∨ Sum.elim head khead e=v then M else N) else 0)+
        (∑ x,∑ t,if ¬(H x t↔H' x t) then (if t=u then M else 0) else 0) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro e _
        by_cases he : ¬(R e↔R' e)
        · rw [if_pos he,if_pos he,markedOmittedPair_spoke_rim]
          exact marked_spoke_rim_pair_cost hm hp hn w B hB (fun W=>(hw W).2) e v u
        · simp only [he,ite_false,le_refl]
      · apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro t _
        by_cases he : ¬(H x t↔H' x t)
        · rw [if_pos he,if_pos he,markedOmittedPair_spokes]
          exact marked_spoke_spoke_pair_cost hm hn w B hB (fun W=>(hw W).2) v x u t
        · simp only [he,ite_false,le_refl]
    _ ≤ d*(3*M+n*N) := by
      calc
        _ ≤ d*((1+1)*M+(Fintype.card V:ℝ)*N)+d*M := by
          convert add_le_add hRcost hHcost using 1 <;> congr!
        _ = _ := by dsimp only [n]; ring
    _ = _ := by dsimp [M,N,C,n];field_simp;ring

end Oberwolfach
