module

public import Oberwolfach.ActualResidualAnchorListProtection
public import Oberwolfach.ReservedSpokeLabelSetExclusions
public import Oberwolfach.MarkedReservedSpokeFromLabels

@[expose] public section
/-! Preserve the actual reserved spoke resources when the old images,
assigned images and free-image lists avoid their physical vertex labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I K J V:Type} [Fintype I] [DecidableEq I] [DecidableEq K] [DecidableEq J]
  [Fintype V] [DecidableEq V] {X:I → Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_residual_reserved_spokes_from_matching_lists
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
    (ψ f:∀i,X i → V) (hψ:∀i,Set.InjOn (ψ i) (↑(a i).oldDomain:Set (X i)))
    (Φ g:∀i,{x // x∈(a i).remaining} → V)
    (Anchors:∀i,Finset {x // x∈(a i).remaining}) (Lists A:I → Finset V)
    (hOldAgree:∀i x,x∈(a i).oldDomain → f i x=ψ i x)
    (hRemAgree:∀i (x:{x // x∈(a i).remaining}),f i x.1=Φ i x)
    (hAnchorAgree:∀i x,x∈Anchors i → Φ i x=g i x)
    (hFree:∀i x,x∉Anchors i → Φ i x∈Lists i)
    (Endpoints Required:I→Finset V) (Kbad:SimpleGraph V) (Lbad:Sym2 V→Finset I)
    (hImages:∀i,(Anchors i).image (g i)=
      (residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1)∪Endpoints i∪Required i)
    (hEnd:∀i v,v∈Endpoints i → ∃e∈Kbad.edgeFinset,v∈e.toFinset ∧ i∈Lbad e)
    (hList:∀e∈Kbad.edgeFinset,∀v∈e.toFinset,∀i∈Lbad e,v∉A i)
    (Outer Reserve:I→Finset V) (Inner:Finset V)
    (hOldOuter:∀i,Disjoint ((a i).oldDomain.image (ψ i)) (Outer i))
    (hAOuter:∀i,A i⊆Outer i)
    (hRequiredInner:∀i,Required i⊆Inner\Reserve i)
    (hReserve:∀i,A i∩Inner⊆Reserve i)
    (hListAvoid:∀i,Disjoint (Lists i) (A i))
    (C:Finset (Finset V⊕(V×I))) (Hold Hnew:Bool → V → I → Prop)
    (Y B:I → Finset V)
    (hMarked:∀v i,Hnew true v i ↔ v∈Y i)
    (hOrdinary:∀v i,Hnew false v i ↔ v∉(Finset.univ.image (f i))∧v∉B i∧v∉Y i)
    (hFixed:∀v i,Sum.inr (v,i)∈C → Hold true v i → v∈Y i)
    (hDisjoint:∀v i,Hold false v i → v∉Y i)
    (hLabel:∀v i,Sum.inr (v,i)∈C → Hold false v i → v∈A i)
    (hBAvoid:∀v i,Sum.inr (v,i)∈C → Hold false v i → v∉B i):
    (∀i,Disjoint (Finset.univ.image (f i)) (A i)) ∧
    (∀b v i,Sum.inr (v,i)∈C → Hold b v i → Hnew b v i) :=by
  have hex:=reserved_spoke_label_set_exclusions (fun i=>(a i).oldDomain) ψ Outer A Required Reserve Inner
    hOldOuter hAOuter hRequiredInner hReserve
  have hAnchor:=actual_residual_listed_anchors_avoid_reserved_labels F hF a ψ hψ g Anchors
    Endpoints Required A Kbad Lbad hImages hEnd hList hex.2 hex.1
  exact actual_residual_reserved_spokes_from_image_exclusions F a hCycle ψ f Φ g Anchors Lists A
    hOldAgree hRemAgree hAnchorAgree hFree hex.1 hAnchor hListAvoid C Hold Hnew Y B
    hMarked hOrdinary hFixed hDisjoint hLabel hBAvoid
end Oberwolfach
