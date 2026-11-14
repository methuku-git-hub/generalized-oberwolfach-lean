module

public import Oberwolfach.ActualResidualReservedMatchingLists
public import Oberwolfach.ActualReservedMatchingListLowerBound
public import Oberwolfach.ActualReservedSpokeInnerExclusions

@[expose] public section
/-! The actual reserved ordinary spokes determine the matching-list
exclusions and the inner forbidden labels used by the residual embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I K J V:Type} [Fintype I] [DecidableEq I] [DecidableEq K] [DecidableEq J]
  [Fintype V] [DecidableEq V] {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem actual_residual_reservation_from_exact_resources
    (F:∀i,SimpleGraph (X i)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
    (ψ f:∀i,X i→V) (hψ:∀i,Set.InjOn (ψ i) (↑(a i).oldDomain:Set (X i)))
    (Φ g:∀i,{x // x∈(a i).remaining}→V)
    (Anchors:∀i,Finset {x // x∈(a i).remaining}) (Lists:I→Finset V)
    (hOldAgree:∀i x,x∈(a i).oldDomain → f i x=ψ i x)
    (hRemAgree:∀i (x:{x // x∈(a i).remaining}),f i x.1=Φ i x)
    (hAnchorAgree:∀i x,x∈Anchors i → Φ i x=g i x)
    (hFree:∀i x,x∉Anchors i → Φ i x∈Lists i)
    (C:Finset (Finset V⊕(V×I))) (Hold Hnew:Bool→V→I→Prop)
    (Outer Y Block:I→Finset V) (Inner:Finset V)
    (hOuter:∀v i,Hold false v i → v∈Outer i)
    (hOldOuter:∀i,Disjoint ((a i).oldDomain.image (ψ i)) (Outer i))
    (hMarked:∀v i,Hnew true v i ↔ v∈Y i)
    (hOrdinary:∀v i,Hnew false v i ↔ v∉(Finset.univ.image (f i))∧v∉Block i∧v∉Y i)
    (hFixed:∀v i,Sum.inr (v,i)∈C → Hold true v i → v∈Y i)
    (hDisjoint:∀v i,Hold false v i → v∉Y i)
    (hBAvoid:∀v i,Sum.inr (v,i)∈C → Hold false v i → v∉Block i)
    (Endpoints Required:I→Finset V) (Kbad:SimpleGraph V) (S:Sym2 V→Finset I) (α:ℝ)
    (hSlack:∀e∈Kbad.edgeFinset,α*Fintype.card V+2*C.card≤((S e).card:ℝ)):
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let Reserve:=fun i=>(Outer i∪Y i)∩Inner
    let Lbad:=reservedSpokeMatchingList S A;
    (∀i,Required i⊆Inner\Reserve i) → (∀i,Disjoint (Lists i) (A i)) →
    (∀i,(Anchors i).image (g i)=
      (residualSubtypeSet (a i).remaining (a i).prescribed).image (fun x=>ψ i x.1)∪Endpoints i∪Required i) →
    (∀i v,v∈Endpoints i → ∃e∈Kbad.edgeFinset,v∈e.toFinset ∧ i∈Lbad e) →
    (∀e∈Kbad.edgeFinset,α*Fintype.card V≤((Lbad e).card:ℝ)) ∧
    (∀i,Disjoint (Finset.univ.image (f i)) (A i)) ∧
    (∀b v i,Sum.inr (v,i)∈C → Hold b v i → Hnew b v i) :=by
  intro A Reserve Lbad hRequired hLists hImages hEnd
  have hcounts:=actual_reserved_matching_list_lower_bound C Hold S Kbad α hSlack
  have hsets:=actual_reserved_spokes_in_outer_and_inner_exclusion C Hold Outer Y Inner hOuter
  have hlabel:∀v i,Sum.inr (v,i)∈C → Hold false v i → v∈A i:=by
    intro v i hC hH
    exact (actual_reserved_ordinary_spoke_labels_mem C Hold i v).mpr ⟨hC,hH⟩
  have hprotected:=actual_residual_reserved_spokes_from_matching_lists F hF a hCycle ψ f hψ Φ g Anchors Lists A
    hOldAgree hRemAgree hAnchorAgree hFree Endpoints Required Kbad Lbad hImages hEnd hcounts.2.1
    Outer Reserve Inner hOldOuter hsets.1 hRequired hsets.2 hLists C Hold Hnew Y Block
    hMarked hOrdinary hFixed hDisjoint hlabel hBAvoid
  exact ⟨hcounts.1,hprotected.1,hprotected.2⟩
end Oberwolfach
