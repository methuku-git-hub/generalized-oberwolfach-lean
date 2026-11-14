module

public import Oberwolfach.HubRowPackingSupport
public import Oberwolfach.PrescribedCoverRootInputs

@[expose] public section

/-! The deep-root wheels add no edge to the protected inner pair. This
checks physical rim edges and spokes separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r nh nr:ℕ}

theorem ordinary_deep_packing_avoids_inner
    (M:Finset (OrdinaryWheel Q F H r)) (I:Finset V) (J:Finset U)
    (u:Fin nh→U) (x:Fin nr→V) (Q₁:SimpleGraph V) (H₁:V→U→Prop)
    (hsupport:∀ W∈M,
      (∃ i,ordinaryWheelHub W=u i ∧ ∀ v∈(ordinaryWheelRim W).support,v∉I) ∨
      (∃ i,ordinaryWheelHub W∉J ∧ ∀ v∈(ordinaryWheelRim W).support,v=x i∨v∉I)):
    Disjoint (M.biUnion ordinaryWheelResources)
      (ordinaryHostResources (spanningRestriction Q₁ I) (fun v a=>H₁ v a∧v∈I∧a∈J)):=by
  apply Finset.disjoint_left.mpr
  intro e he hi
  obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
  cases e with
  | inl e=>
    have hR:=(ordinaryWheelResources_rim W e).mp he
    have hI:=(ordinaryHostResources_rim (spanningRestriction Q₁ I) _ e).mp hi
    induction e using Sym2.ind with
    | _ v w=>
      have hv:v∈I:=((spanningRestriction_adj Q₁ I v w).mp hI).2.1
      have hw:w∈I:=((spanningRestriction_adj Q₁ I v w).mp hI).2.2
      rcases hsupport W hW with ⟨i,_,hs⟩|⟨i,_,hs⟩
      · exact hs v hR.mem_support_left hv
      · have hvx:v=x i:=(hs v hR.mem_support_left).resolve_right (fun hn=>hn hv)
        have hwx:w=x i:=(hs w hR.mem_support_right).resolve_right (fun hn=>hn hw)
        exact hR.ne (hvx.trans hwx.symm)
  | inr va=>
    obtain ⟨hhub,hv⟩:=(ordinaryWheelResources_spoke W va.1 va.2).mp he
    obtain ⟨_,hvI,haJ⟩:=(ordinaryHostResources_spoke (spanningRestriction Q₁ I) _ va.1 va.2).mp hi
    rcases hsupport W hW with ⟨i,_,hs⟩|⟨i,hJ,_⟩
    · exact hs va.1 hv hvI
    · exact hJ (hhub.symm ▸ haJ)

end Oberwolfach
