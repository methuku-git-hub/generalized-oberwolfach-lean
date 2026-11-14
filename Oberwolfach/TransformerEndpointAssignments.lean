module

public import Oberwolfach.GraphTwoRootReplacement
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! The two endpoints of each incident spoke are matched bijectively
with the incident rim edges. A permutation without fixed points assigns
rim-edge hubs to different rim paths, including at vertices of degree two. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

 theorem finRotate_ne_self_of_two_le {n:ℕ} (hn:2≤n) (i:Fin n):finRotate n i≠i:=by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega: n≠0)
  intro he
  have hh:=congrArg Fin.val he
  rw [coe_finRotate] at hh
  split_ifs at hh with hi
  · have hi':i.val=k:=congrArg Fin.val hi
    omega
  · omega

 theorem finite_permutation_without_fixed_points (I:Type*) [Fintype I]
    (hcard:Fintype.card I≠1):∃ σ:Equiv.Perm I,∀ i,σ i≠i:=by
  let e:=Fintype.equivFin I
  refine ⟨(e.trans (finRotate (Fintype.card I))).trans e.symm,?_⟩
  intro i hi
  have hpos:0<Fintype.card I:=Fintype.card_pos_iff.mpr ⟨i⟩
  have hh:=congrArg e hi
  simp only [Equiv.trans_apply,Equiv.apply_symm_apply] at hh
  exact finRotate_ne_self_of_two_le (by omega) (e i) hh

variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

 theorem transformer_endpoint_assignments (Q:SimpleGraph V) (H:V→U→Prop)
    (hbalance:∀ v,Q.degree v=2*((Finset.univ:Finset U).filter (H v)).card):
    ∃ (σ:∀ v,Equiv.Perm (Q.neighborSet v))
      (b:∀ v,Q.neighborSet v≃({u:U // H v u}×Fin 2)),
      (∀ v w,σ v w≠w) ∧
      (∀ v w,s(v,(σ v w).val)≠s(v,w.val)):=by
  have hcard (v:V):Fintype.card (Q.neighborSet v)=2*Fintype.card {u:U // H v u}:=by
    rw [Set.fintypeCard_eq_ncard,SimpleGraph.ncard_neighborSet]
    simpa only [Fintype.card_subtype,Finset.card_filter] using hbalance v
  have hperm (v:V):∃ σ:Equiv.Perm (Q.neighborSet v),∀ w,σ w≠w:=by
    apply finite_permutation_without_fixed_points
    rw [hcard]
    omega
  choose σ hσ using hperm
  have hb (v:V):Fintype.card (Q.neighborSet v)=Fintype.card ({u:U // H v u}×Fin 2):=by
    rw [Fintype.card_prod,Fintype.card_fin,hcard,Nat.mul_comm]
  refine ⟨σ,fun v=>Fintype.equivOfCardEq (hb v),hσ,?_⟩
  intro v w he
  exact hσ v w (Subtype.ext (sym2_fixed_endpoint_injective v he))

 theorem transformer_endpoint_sum {v:V} (Q:SimpleGraph V) (H:V→U→Prop)
    (b:Q.neighborSet v≃({u:U // H v u}×Fin 2))
    (f:({u:U // H v u}×Fin 2)→ℤ):
    (∑ w:Q.neighborSet v,f (b w))=∑ u:{u:U // H v u},∑ i:Fin 2,f (u,i):=by
  rw [Equiv.sum_comp,Fintype.sum_prod_type]

end Oberwolfach
