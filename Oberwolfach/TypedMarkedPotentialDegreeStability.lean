module

public import Oberwolfach.TypedMarkedPairCosts
public import Oberwolfach.OccurrenceIncidentWeights

@[expose] public section

/-! Deterministic stability on the full typed potential universe. Both
spoke types and the two rim types remain distinct; the tested root is
omitted, and the fixed parent weights are not recomputed. -/
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
  (hm : 3≤m) (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
  (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
  (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
  (R R' : E⊕K → Prop) (H H' : Bool → V → U → Prop) (d : ℝ) (hd : 0≤d)
  (hout : ∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim tail ktail e=x then (1:ℝ) else 0)≤d)
  (hin : ∀ x,(∑ e,if ¬(R e↔R' e) ∧ Sum.elim head khead e=x then (1:ℝ) else 0)≤d)
  (hHout : ∀ j x,(∑ u,bipAdj (fun x u=>¬(H j x u↔H' j x u)) x u)≤d)
  (hHin : ∀ j u,(∑ x,bipAdj (fun x u=>¬(H j x u↔H' j x u)) x u)≤d)
include hm hn hu hB hw hd hout hin hHout hHin

theorem typedMarkedPotentialLoad_rim_degree_stability (e : E⊕K) :
    |typedMarkedPotentialLoad w R' H' (Sum.inl e)-typedMarkedPotentialLoad w R H (Sum.inl e)|≤
      11*((m:ℝ)+1)^4*B*d/Fintype.card V := by
  let n : ℝ := Fintype.card V
  let C : ℝ := ((m:ℝ)+1)^4*B
  let M : ℝ := C/n
  let N : ℝ := C/n^2
  let S : Finset V := {Sum.elim tail ktail e,Sum.elim head khead e}
  have hnR : 0<n := by dsimp [n];exact_mod_cast hn
  have hM : 0≤M := by dsimp [M,C];positivity
  have hN : 0≤N := by dsimp [N,C];positivity
  have hS : (S.card : ℝ)≤2 := by
    have hh : S.card≤2 := by dsimp [S];exact (Finset.card_insert_le _ _).trans (by simp)
    exact_mod_cast hh
  have hRcost := occurrence_root_incident_cost (Sum.elim tail ktail) (Sum.elim head khead)
    (fun e=>¬(R e↔R' e)) d (fun x=>by convert hout x using 1 <;> congr!)
      (fun x=>by convert hin x using 1 <;> congr!) S S M N hM hN
  have hHcost (j : Bool) := relation_root_incident_cost (fun v u=>¬(H j v u↔H' j v u)) d
    (hHout j) (hHin j) S ∅ M N hM hN
  simp only [Finset.notMem_empty,or_false,Finset.card_empty,Nat.cast_zero,add_zero] at hHcost
  have hstart := typedMarkedPotentialLoad_change w (fun W=>(hw W).1) R R' H H' (Sum.inl e)
  apply hstart.trans
  calc
    _ ≤ (∑ f,if ¬(R f↔R' f) then (if Sum.elim tail ktail f∈S ∨ Sum.elim head khead f∈S then M else N) else 0)+
        (∑ j,∑ v,∑ u,if ¬(H j v u↔H' j v u) then (if v∈S then M else N) else 0) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro f _
        by_cases hf : ¬(R f↔R' f)
        · rw [if_pos hf,if_pos hf]
          exact typedMarkedPair_rim_rim hm hn hu w B hB hw e f
        · simp only [hf,ite_false,le_refl]
      · apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro v _
        apply Finset.sum_le_sum
        intro u _
        by_cases hf : ¬(H j v u↔H' j v u)
        · rw [if_pos hf,if_pos hf]
          exact typedMarkedPair_rim_spoke hm hn w B hB hw e j v u
        · simp only [hf,ite_false,le_refl]
    _ ≤ d*(8*M+3*n*N) := by
      simp only [Fintype.sum_bool]
      calc
        _ ≤ d*((S.card+S.card:ℝ)*M+(Fintype.card V:ℝ)*N)+
            (d*((S.card:ℝ)*M+(Fintype.card V:ℝ)*N)+d*((S.card:ℝ)*M+(Fintype.card V:ℝ)*N)) := by
          convert add_le_add hRcost (add_le_add (hHcost true) (hHcost false)) using 1 <;> congr!
        _ ≤ _ := by
          have hs := mul_le_mul_of_nonneg_right hS hM
          have hs' := mul_le_mul_of_nonneg_left hs hd
          dsimp only [n]
          nlinarith only [hs']
    _ = _ := by dsimp [M,N,C,n];field_simp;ring

omit hu in
theorem typedMarkedPotentialLoad_spoke_degree_stability (j : Bool) (v : V) (u : U) :
    |typedMarkedPotentialLoad w R' H' (Sum.inr (j,v,u))-typedMarkedPotentialLoad w R H (Sum.inr (j,v,u))|≤
      5*((m:ℝ)+1)^4*B*d/Fintype.card V := by
  let n : ℝ := Fintype.card V
  let C : ℝ := ((m:ℝ)+1)^4*B
  let M : ℝ := C/n
  let N : ℝ := C/n^2
  have hnR : 0<n := by dsimp [n];exact_mod_cast hn
  have hM : 0≤M := by dsimp [M,C];positivity
  have hN : 0≤N := by dsimp [N,C];positivity
  have hRcost := occurrence_root_incident_cost (Sum.elim tail ktail) (Sum.elim head khead)
    (fun e=>¬(R e↔R' e)) d (fun x=>by convert hout x using 1 <;> congr!)
      (fun x=>by convert hin x using 1 <;> congr!) {v} {v} M N hM hN
  have hHcost (k : Bool) := relation_root_incident_cost (fun v u=>¬(H k v u↔H' k v u)) d
    (hHout k) (hHin k) ∅ {u} M 0 hM (by norm_num)
  simp only [Finset.card_singleton,Nat.cast_one,Finset.mem_singleton] at hRcost
  simp only [Finset.card_empty,Nat.cast_zero,Finset.card_singleton,Nat.cast_one,
    Finset.notMem_empty,Finset.mem_singleton,false_or,zero_add,mul_zero,add_zero,one_mul] at hHcost
  have hstart := typedMarkedPotentialLoad_change w (fun W=>(hw W).1) R R' H H' (Sum.inr (j,v,u))
  apply hstart.trans
  calc
    _ ≤ (∑ e,if ¬(R e↔R' e) then (if Sum.elim tail ktail e=v ∨ Sum.elim head khead e=v then M else N) else 0)+
        (∑ k,∑ x,∑ t,if ¬(H k x t↔H' k x t) then (if t=u then M else 0) else 0) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro e _
        by_cases he : ¬(R e↔R' e)
        · rw [if_pos he,if_pos he]
          exact typedMarkedPair_spoke_rim hm hn w B hB hw e j v u
        · simp only [he,ite_false,le_refl]
      · apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro t _
        by_cases he : ¬(H k x t↔H' k x t)
        · rw [if_pos he,if_pos he]
          exact typedMarkedPair_spoke_spoke hm hn w B hB hw j k v x u t
        · simp only [he,ite_false,le_refl]
    _ ≤ d*(4*M+n*N) := by
      simp only [Fintype.sum_bool]
      calc
        _ ≤ d*((1+1)*M+(Fintype.card V:ℝ)*N)+(d*M+d*M) := by
          convert add_le_add hRcost (add_le_add (hHcost true) (hHcost false)) using 1 <;> congr!
        _ = _ := by dsimp only [n];ring
    _ = _ := by dsimp [M,N,C,n];field_simp;ring

end Oberwolfach
