module

public import Oberwolfach.LongRawIncidenceFamily
public import Oberwolfach.MarkedIncidentResources

@[expose] public section
/-! The exact auxiliary and spoke tests have linear size before and after
restriction. The auxiliary bound counts both ordinary and marked endpoints;
the spoke bounds retain the selected type and the original hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_incidence_set_card_le_full
    (S:Finset (LongRawHubResource n U)) (i:LongRawIncidenceIndex n U):
    (longRawIncidenceSet S i).card≤
      ((Finset.univ:Finset (LongRawHubResource n U)).filter (longRawResourceIncident i)).card :=by
  apply Finset.card_le_card_of_injOn (fun v:S=>v.val)
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩
  · intro v hv w hw h
    exact Subtype.ext h

theorem long_raw_auxiliary_incidence_card_le
    (S:Finset (LongRawHubResource n U)) (x:Fin n):
    (longRawIncidenceSet S (.inl x)).card≤4*n :=by
  apply (long_raw_incidence_set_card_le_full S (.inl x)).trans
  rw [filter_card_sum_type,filter_card_sum_type]
  simp only [longRawResourceIncident,Finset.filter_false,Finset.card_empty,add_zero]
  have h:=paired_incidence_card (Prod.fst:Fin n×Fin n→Fin n) Prod.snd
    (fun _ _ h=>h) x
  simp only [Fintype.card_fin] at h
  have hh:=Nat.add_le_add h h
  have heq:2*n+2*n=4*n:=by omega
  rw [heq] at hh
  convert hh using 1 <;> congr 3

theorem long_raw_vertex_spoke_incidence_card_le
    (S:Finset (LongRawHubResource n U)) (typ:Bool) (x:Fin n):
    (longRawIncidenceSet S (.inr (typ,.inl x))).card≤Fintype.card U :=by
  apply (long_raw_incidence_set_card_le_full S (.inr (typ,.inl x))).trans
  rw [filter_card_sum_type]
  simp only [longRawResourceIncident,Finset.filter_false,Finset.card_empty,zero_add]
  have h:=paired_fiber_card (fun z:Bool×Fin n×U=>(z.1,z.2.1)) (fun z=>z.2.2)
    (by
      intro a b h
      apply Prod.ext
      · exact congrArg (fun z=>(z.1).1) h
      · apply Prod.ext
        · exact congrArg (fun z=>(z.1).2) h
        · exact congrArg (fun z:(Bool×Fin n)×U=>z.2) h) (typ,x)
  simpa only [Prod.mk.injEq,eq_comm] using h

theorem long_raw_hub_spoke_incidence_card_le
    (S:Finset (LongRawHubResource n U)) (typ:Bool) (u:U):
    (longRawIncidenceSet S (.inr (typ,.inr u))).card≤n :=by
  apply (long_raw_incidence_set_card_le_full S (.inr (typ,.inr u))).trans
  rw [filter_card_sum_type]
  simp only [longRawResourceIncident,Finset.filter_false,Finset.card_empty,zero_add]
  have h:=paired_fiber_card (fun z:Bool×Fin n×U=>(z.1,z.2.2)) (fun z=>z.2.1)
    (by
      intro a b h
      apply Prod.ext
      · exact congrArg (fun z=>(z.1).1) h
      · apply Prod.ext
        · exact congrArg (fun z:(Bool×U)×Fin n=>z.2) h
        · exact congrArg (fun z=>(z.1).2) h) (typ,u)
  simpa only [Prod.mk.injEq,eq_comm,Fintype.card_fin] using h

end Oberwolfach
