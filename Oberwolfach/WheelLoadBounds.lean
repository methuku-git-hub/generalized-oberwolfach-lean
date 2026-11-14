module

public import Oberwolfach.RootWheelCaps

@[expose] public section

/-! Incidence counts for finite wheel families, including the bounds used
when free rim vertices and free hubs are excluded after reaching a cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type*} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

def wheelRimLoad (C:I→OrdinaryWheel Q F H r) (a:V):ℕ :=
  (Finset.univ.filter (fun i=>a∈(ordinaryWheelRim (C i)).support)).card

def wheelHubLoad (C:I→OrdinaryWheel Q F H r) (u:U):ℕ :=
  (Finset.univ.filter (fun i=>ordinaryWheelHub (C i)=u)).card

theorem wheelRimLoad_total (C:I→OrdinaryWheel Q F H r):
    ∑ a,wheelRimLoad C a=Fintype.card I*r:=by
  simp only [wheelRimLoad,Finset.card_filter]
  rw [Finset.sum_comm]
  have hc (i:I):(∑ a:V,if a∈(ordinaryWheelRim (C i)).support then (1:ℕ) else 0) = r:=by
    have he:Finset.univ.filter (fun a=>a∈(ordinaryWheelRim (C i)).support)=(ordinaryWheelRim (C i)).support.toFinset:=by
      ext a;simp
    rw [←Finset.card_filter,he]
    exact (C i).val.1.val.property.support_card
  simp only [hc,Finset.sum_const,Finset.card_univ,smul_eq_mul]

theorem wheelHubLoad_total (C:I→OrdinaryWheel Q F H r):
    ∑ u,wheelHubLoad C u=Fintype.card I:=by
  simp only [wheelHubLoad,Finset.card_filter]
  rw [Finset.sum_comm]
  simp

theorem wheelRimLoad_saturated (C:I→OrdinaryWheel Q F H r) (K:ℕ):
    K*(Finset.univ.filter (fun a=>K≤wheelRimLoad C a)).card≤Fintype.card I*r:=by
  calc
    _ = ∑ a∈Finset.univ.filter (fun a=>K≤wheelRimLoad C a),K:=by simp [Nat.mul_comm]
    _ ≤ ∑ a∈Finset.univ.filter (fun a=>K≤wheelRimLoad C a),wheelRimLoad C a:=
      Finset.sum_le_sum (fun a ha=>(Finset.mem_filter.mp ha).2)
    _ ≤ ∑ a,wheelRimLoad C a:=Finset.sum_le_univ_sum_of_nonneg (fun _=>Nat.zero_le _)
    _ = _:=wheelRimLoad_total C

theorem wheelHubLoad_saturated (C:I→OrdinaryWheel Q F H r) (K:ℕ):
    K*(Finset.univ.filter (fun u=>K≤wheelHubLoad C u)).card≤Fintype.card I:=by
  calc
    _ = ∑ u∈Finset.univ.filter (fun u=>K≤wheelHubLoad C u),K:=by simp [Nat.mul_comm]
    _ ≤ ∑ u∈Finset.univ.filter (fun u=>K≤wheelHubLoad C u),wheelHubLoad C u:=
      Finset.sum_le_sum (fun u hu=>(Finset.mem_filter.mp hu).2)
    _ ≤ ∑ u,wheelHubLoad C u:=Finset.sum_le_univ_sum_of_nonneg (fun _=>Nat.zero_le _)
    _ = _:=wheelHubLoad_total C

theorem wheelRimLoad_degree (C:I→OrdinaryWheel Q F H r) (a:V):
    (wheelFamilyRim C).degree a≤2*wheelRimLoad C a:=by
  have hh:=graph_iSup_global_degree_bound (fun i=>ordinaryWheelRim (C i))
    (fun i=>(ordinaryWheelRim (C i)).support.toFinset) 2
    (by intro i x y h;exact ⟨Set.mem_toFinset.mpr h.mem_support_left,Set.mem_toFinset.mpr h.mem_support_right⟩)
    (by
      intro i v
      have hC:IsEmbeddedCycle (ordinaryWheelRim (C i)) r:=(C i).val.1.val.property
      rcases hC.degree_zero_or_two v with h|h <;> omega) a
  simpa only [wheelFamilyRim,Set.mem_toFinset,wheelRimLoad] using hh

theorem wheelRimLoad_spoke_row (C:I→OrdinaryWheel Q F H r) (a:V):
    (Finset.univ.filter (fun u=>wheelFamilySpokes C a u)).card≤wheelRimLoad C a:=by
  have hs:Finset.univ.filter (fun u=>wheelFamilySpokes C a u)=
    (Finset.univ.filter (fun i=>a∈(ordinaryWheelRim (C i)).support)).image (fun i=>ordinaryWheelHub (C i)):=by
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image,wheelFamilySpokes]
    constructor
    · rintro ⟨i,hi,ha⟩;exact ⟨i,ha,hi⟩
    · rintro ⟨i,ha,hi⟩;exact ⟨i,hi,ha⟩
  rw [hs]
  exact Finset.card_image_le

theorem wheelHubLoad_spoke_column (C:I→OrdinaryWheel Q F H r) (u:U):
    (Finset.univ.filter (fun a=>wheelFamilySpokes C a u)).card≤wheelHubLoad C u*r:=by
  have he:Finset.univ.filter (fun a=>wheelFamilySpokes C a u)=
      (Finset.univ.filter (fun i=>ordinaryWheelHub (C i)=u)).biUnion
        (fun i=>(ordinaryWheelRim (C i)).support.toFinset):=by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,Set.mem_toFinset,wheelFamilySpokes]
  rw [he]
  calc
    _ ≤ ∑ i∈Finset.univ.filter (fun i=>ordinaryWheelHub (C i)=u),(ordinaryWheelRim (C i)).support.toFinset.card:=Finset.card_biUnion_le
    _ = _:=by
      have hc (i:I):(ordinaryWheelRim (C i)).support.toFinset.card=r:=(C i).val.1.val.property.support_card
      simp only [hc,Finset.sum_const,smul_eq_mul,wheelHubLoad]

theorem wheelRimLoad_snoc {n:ℕ} (C:Fin n→OrdinaryWheel Q F H r) (B:OrdinaryWheel Q F H r) (a:V):
    wheelRimLoad (Fin.snoc C B) a=wheelRimLoad C a+(if a∈(ordinaryWheelRim B).support then 1 else 0):=by
  simp only [wheelRimLoad,Finset.card_filter,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]

theorem wheelHubLoad_snoc {n:ℕ} (C:Fin n→OrdinaryWheel Q F H r) (B:OrdinaryWheel Q F H r) (u:U):
    wheelHubLoad (Fin.snoc C B) u=wheelHubLoad C u+(if ordinaryWheelHub B=u then 1 else 0):=by
  simp only [wheelHubLoad,Finset.card_filter,Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]

end Oberwolfach
