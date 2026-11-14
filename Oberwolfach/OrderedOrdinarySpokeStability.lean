module

public import Oberwolfach.OrderedOrdinarySharpSpokePairs
public import Oberwolfach.ResourceRootOmittedLoads
public import Oberwolfach.RelationIncidentWeights

@[expose] public section
/-! Changes to actual ordinary spokes preserve each original ordered-wheel
root load, with a loss controlled by their maximum row and column degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

def ordinaryPotentialKeep (R:V×V→Prop) (H:V→U→Prop): (V×V)⊕(V×U)→Prop :=
  Sum.elim R (fun vu=>H vu.1 vu.2)

theorem ordered_ordinary_spoke_stability_rim
    (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B d:ℝ) (hB:0≤B) (hd:0≤d)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (R:V×V→Prop) (H H':V→U→Prop)
    (hrow:∀v,(∑u,bipAdj (fun x u=>¬(H x u↔H' x u)) v u)≤d)
    (hcol:∀u,(∑v,bipAdj (fun x u=>¬(H x u↔H' x u)) v u)≤d)
    (x y:V):
    |resourceRootOmittedLoad orderedOrdinaryResources w (ordinaryPotentialKeep R H') (Sum.inl (x,y))-
      resourceRootOmittedLoad orderedOrdinaryResources w (ordinaryPotentialKeep R H) (Sum.inl (x,y))|≤
      3*((m:ℝ)+1)^3*B*d/Fintype.card V := by
  let n:ℝ:=Fintype.card V
  let C:ℝ:=((m:ℝ)+1)^3*B
  let M:ℝ:=C/n
  let N:ℝ:=C/n^2
  let S:Finset V:={x,y}
  let D:V→U→Prop:=fun v u=>¬(H v u↔H' v u)
  have hnR:0<n:=by dsimp [n];exact_mod_cast hn
  have hM:0≤M:=by dsimp [M,C];positivity
  have hN:0≤N:=by dsimp [N,C];positivity
  have hS:(S.card:ℝ)≤2:=by
    have h:S.card≤2:=by dsimp [S];exact (Finset.card_insert_le _ _).trans (by simp)
    exact_mod_cast h
  have hc:=relation_root_incident_cost D d hrow hcol S ∅ M N hM hN
  simp only [Finset.notMem_empty,or_false,Finset.card_empty,Nat.cast_zero,add_zero] at hc
  have hstart:=resourceRootOmittedLoad_change orderedOrdinaryResources w (fun W=>(hw W).1)
    (ordinaryPotentialKeep R H) (ordinaryPotentialKeep R H') (Sum.inl (x,y))
  apply hstart.trans
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,ordinaryPotentialKeep,Sum.elim_inl,Sum.elim_inr,
    iff_self,not_true_eq_false,ite_false,Finset.sum_const_zero,zero_add]
  calc
    _ ≤ ∑ v,∑ u,if D v u then (if v∈S then M else N) else 0 := by
      apply Finset.sum_le_sum;intro v _
      apply Finset.sum_le_sum;intro u _
      by_cases hv:D v u
      · rw [if_pos hv,if_pos hv]
        rw [orderedOrdinary_omitted_pair_symm]
        by_cases hmem:v∈S
        · rw [if_pos hmem]
          have hcoarse:=orderedOrdinary_spoke_rim_pair_bound hm hn w B hB hw v u x y
          have hpow:((m:ℝ)+1)^2≤((m:ℝ)+1)^3:=by
            have hb:(1:ℝ)≤(m:ℝ)+1:=by have hh:(0:ℝ)≤m:=Nat.cast_nonneg m;linarith
            calc
              _ = ((m:ℝ)+1)^2*1:=by ring
              _ ≤ ((m:ℝ)+1)^2*((m:ℝ)+1):=mul_le_mul_of_nonneg_left hb (by positivity)
              _ = _:=by ring
          exact hcoarse.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hB) hnR.le)
        · rw [if_neg hmem]
          have hx:v≠x:=by intro h;apply hmem;simp [S,h]
          have hy:v≠y:=by intro h;apply hmem;simp [S,h]
          exact ordered_ordinary_spoke_rim_three_vertices hm hn w B hB hw v x y u hx hy
      · simp [D,hv]
    _ ≤ d*((S.card:ℝ)*M+n*N):=hc
    _ ≤ 3*C*d/n := by
      calc
        _ ≤ d*(2*M+n*N):=mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right hS hM) (le_refl (n*N))) hd
        _ = _ := by dsimp [M,N];field_simp;ring
    _ = _ := by dsimp [C,n];ring

theorem ordered_ordinary_spoke_stability_spoke
    (hm:2≤m) (hn:0<Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B d:ℝ) (hB:0≤B) (hd:0≤d)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (R:V×V→Prop) (H H':V→U→Prop)
    (hrow:∀v,(∑u,bipAdj (fun x u=>¬(H x u↔H' x u)) v u)≤d)
    (hcol:∀u,(∑v,bipAdj (fun x u=>¬(H x u↔H' x u)) v u)≤d)
    (v:V) (u:U):
    |resourceRootOmittedLoad orderedOrdinaryResources w (ordinaryPotentialKeep R H') (Sum.inr (v,u))-
      resourceRootOmittedLoad orderedOrdinaryResources w (ordinaryPotentialKeep R H) (Sum.inr (v,u))|≤
      ((m:ℝ)+1)^2*B*d/Fintype.card V := by
  let n:ℝ:=Fintype.card V
  let C:ℝ:=((m:ℝ)+1)^2*B
  let M:ℝ:=C/n
  let D:V→U→Prop:=fun v u=>¬(H v u↔H' v u)
  have hnR:0<n:=by dsimp [n];exact_mod_cast hn
  have hM:0≤M:=by dsimp [M,C];positivity
  have hc:=relation_root_incident_cost D d hrow hcol ∅ {u} M 0 hM (by norm_num)
  simp only [Finset.card_empty,Nat.cast_zero,Finset.card_singleton,Nat.cast_one,
    Finset.notMem_empty,false_or,zero_add,mul_zero,add_zero,one_mul] at hc
  have hstart:=resourceRootOmittedLoad_change orderedOrdinaryResources w (fun W=>(hw W).1)
    (ordinaryPotentialKeep R H) (ordinaryPotentialKeep R H') (Sum.inr (v,u))
  apply hstart.trans
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,ordinaryPotentialKeep,Sum.elim_inl,Sum.elim_inr,
    iff_self,not_true_eq_false,ite_false,Finset.sum_const_zero,zero_add]
  calc
    _ ≤ ∑ x,∑ t,if D x t then (if t=u then M else 0) else 0 := by
      apply Finset.sum_le_sum;intro x _
      apply Finset.sum_le_sum;intro t _
      by_cases ht:D x t
      · rw [if_pos ht,if_pos ht]
        by_cases he:t=u
        · rw [if_pos he];subst t
          exact orderedOrdinary_spoke_spoke_pair_bound hm hn w B hB hw v x u u
        · rw [if_neg he]
          exact le_of_eq (ordered_ordinary_spokes_different_hubs_zero w v x u t (Ne.symm he))
      · simp [D,ht]
    _ ≤ d*M:=by simpa only [Finset.mem_singleton] using hc
    _ = _ := by dsimp [M,C,n];ring
end Oberwolfach
