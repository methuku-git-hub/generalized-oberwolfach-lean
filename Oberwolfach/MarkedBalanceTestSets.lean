module

public import Oberwolfach.MarkedBoundaryPhysicalCoordinates
public import Oberwolfach.MarkedIncidentResources
public import Oberwolfach.MarkedBoundaryRetainedHost
public import Oberwolfach.MarkedPackingTransport

@[expose] public section

/-! Fixed incidence sets for the six degree terms in the four marked
balance equations. They use auxiliary heads; their coins use physical heads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

def markedBalanceTerm (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (r:V⊕U) (j:Fin 6):MarkedActiveEdge E K H₀ HK→Prop:=
  match r with
  | Sum.inl v=>Sum.elim (Sum.elim
      (fun e=>(j=0∧tail e=v)∨(j=2∧head e=v))
      (fun e=>(j=1∧ktail e=v)∨(j=3∧khead e=v)))
      (fun z=>z.val.1=v∧((j=4∧H₀ z.val.1 z.val.2)∨(j=5∧HK z.val.1 z.val.2)))
  | Sum.inr u=>Sum.elim (fun _=>False)
      (fun z=>z.val.2=u∧((j=4∧H₀ z.val.1 z.val.2)∨(j=5∧HK z.val.1 z.val.2)))

def markedBalanceTermSet (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (r:V⊕U) (j:Fin 6):Finset (MarkedActiveEdge E K H₀ HK):=
  Finset.univ.filter (markedBalanceTerm tail head ktail khead H₀ HK r j)

theorem markedBalanceTermSet_incident (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (r:V⊕U) (j:Fin 6) (a:MarkedActiveEdge E K H₀ HK)
    (ha:a∈markedBalanceTermSet tail head ktail khead H₀ HK r j):
    markedActiveAuxTail tail ktail H₀ HK a=r∨markedActiveAuxHead head khead H₀ HK a=r:=by
  have h:=(Finset.mem_filter.mp ha).2
  rcases r with v|u <;> rcases a with (a|a)|a <;>
    simp only [markedBalanceTerm,markedActiveAuxTail,markedActiveAuxHead,Sum.elim_inl,
      Sum.elim_inr,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h ⊢ <;> tauto

theorem markedBalanceTermSet_card (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (r:V⊕U) (j:Fin 6):
    (markedBalanceTermSet tail head ktail khead H₀ HK r j).card≤4*Fintype.card (V⊕U):=by
  have hsub:markedBalanceTermSet tail head ktail khead H₀ HK r j⊆
      markedIncidentEdges tail head ktail khead π H₀ HK false r:=by
    intro a ha
    have h:=markedBalanceTermSet_incident tail head ktail khead H₀ HK r j a ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases r with v|u <;> rcases a with (a|a)|a <;>
      simpa only [markedResourceIncident,markedActiveAuxTail,markedActiveAuxHead,
        Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl,
        Bool.false_eq_true,ite_false,false_or,or_false] using h
  have hc:=(Finset.card_le_card hsub).trans (markedIncidentEdges_card_bound tail head ktail khead π H₀ HK hp false r)
  simp only [Fintype.card_sum]
  omega

theorem marked_active_reservation_complement (tail head:E→V) (ktail khead:K→V)
    (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (X:Finset V) (Z:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (a:MarkedActiveEdge E K H₀ HK):
    markedActiveRetained
      (fun e=>¬markedBoundaryRimAllowed π X σ false (tail e) (head e))
      (fun e=>¬markedBoundaryRimAllowed π X σ true (ktail e) (khead e))
      (fun x u=>H₀ x u∧¬markedBoundarySpokeAllowed X Z σ x u)
      (fun x u=>HK x u∧¬markedBoundarySpokeAllowed X Z σ x u) a↔
    ¬((markedActiveAuxTail tail ktail H₀ HK a∈ordinaryInnerVertices X Z∧
       markedActiveAuxHead head khead H₀ HK a∈ordinaryInnerVertices X Z)∨
      ((markedActiveAuxTail tail ktail H₀ HK a∈ordinaryInnerVertices X Z∨
        markedActiveAuxHead head khead H₀ HK a∈ordinaryInnerVertices X Z)∧
        σ (markedActivePhysicalCoin tail head ktail khead π H₀ HK a)=true)):=by
  rcases a with (a|a)|a
  · simp only [markedActiveRetained,markedBoundaryRimAllowed,markedActiveAuxTail,markedActiveAuxHead,
      markedActivePhysicalCoin,markedArcPhysicalCoin,ordinaryPhysicalResource,Sum.elim_inl,
      Sum.elim_inr,ordinaryInnerVertices_left,Bool.false_eq_true,ite_false,Sym2.map_mk]
  · simp only [markedActiveRetained,markedBoundaryRimAllowed,markedActiveAuxTail,markedActiveAuxHead,
      markedActivePhysicalCoin,markedArcPhysicalCoin,ordinaryPhysicalResource,Sum.elim_inl,
      Sum.elim_inr,ordinaryInnerVertices_left,ite_true,Sym2.map_mk]
  · have hp:=a.property
    simp only [markedActiveRetained,markedBoundarySpokeAllowed,markedActiveAuxTail,markedActiveAuxHead,
      markedActivePhysicalCoin,ordinaryPhysicalResource,Sum.elim_inr,ordinaryInnerVertices_left,ordinaryInnerVertices_right]
    tauto
end Oberwolfach
