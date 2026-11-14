module

public import Oberwolfach.OrdinaryCompletedActualComplementRemainder
public import Oberwolfach.OrdinaryProtectedPairWithActualAbsorber
public import Oberwolfach.OrdinaryForbiddenCompletionInputs
public import Oberwolfach.OrdinaryProtectedPairSampleAgreement

@[expose] public section
/-! The actual edited remainder has the same protected pair and fixed
absorber, and avoids forbidden edges, under local spoke avoidance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_postmatching_complement_local_pair_and_absorber {n q:ℕ}
    (Target Sample Reference Protect Bad:SimpleGraph (Fin n)) (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Href:Fin n→Fin q→Prop) (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Old New:Fin q→Finset (Sym2 (Fin n))) (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hRef:Reference≤Sample) (hBad:Disjoint Reference Bad)
    (hAgreement:∀v∈Inner,∀w∈Inner,Target.Adj v w↔Sample.Adj v w)
    (hProtect:Protect≤Reference) (hInnerProtect:spanningRestriction Reference Inner≤Protect)
    (hA:A⊆ordinaryHostResources Reference Href)
    (hReserveProtect:ordinaryResourceRim Reference A≤Protect)
    (hReserveTarget:ordinaryResourceRim Reference A≤Target)
    (hRim:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→
      (Target\Protect).Adj (f u x) (f u y))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=Old u∪New u)
    (hcover:∀e∈(ordinaryPostmatchingRequired Target Sample Reference Bad (prescribedPhysicalUnion Old) Inner).edgeFinset,∃u,e∈New u)
    (hAvoidLocal:∀u,u∈Hubs→∀x,f u x∈Inner→¬Href (f u x) u)
    (hAvoidAbs:∀u x,f u x∉ordinaryReservoirSpokeLabels A u)
    (hSpokeCover:∀u v,v∈ordinaryInnerSpokeTargets Inner Hubs Href u→∃x,f u x=v):
    let R:=Target\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u);
    A⊆ordinaryHostResources R H ∧
    (∀v∈Inner,∀w∈Inner,(R.Adj v w↔Reference.Adj v w)) ∧
    (∀v∈Inner,∀u∈Hubs,(H v u↔Href v u)) ∧ Disjoint R Bad :=by
  intro R H
  have hrem:=ordinary_completed_actual_complement_remainder Fs C f Old New Target Sample Reference Protect Bad Inner
    hRef hProtect hBad hInnerProtect hAgreement hRim hpartition hcover
  have hres:=ordinary_protected_reservoir_survives_actual_label_avoidance Reference Target Fs C f Href A hA hReserveTarget
    (by
      intro u x y hxy
      have hh:=hRim u x y hxy
      exact ⟨hh.1,fun hr=>hh.2 (hReserveProtect hr)⟩) hAvoidAbs
  have hspoke:∀v∈Inner,∀u∈Hubs,(H v u↔Href v u):=by
    intro v hv u hu
    constructor
    · intro hnot
      by_contra hn
      have hT:v∈ordinaryInnerSpokeTargets Inner Hubs Href u:=by
        simp [ordinaryInnerSpokeTargets,hu,hv,hn]
      obtain ⟨x,hx⟩:=hSpokeCover u v hT
      exact hnot ⟨x,hx⟩
    · intro h hx
      obtain ⟨x,hx⟩:=hx
      exact hAvoidLocal u hu x (hx ▸ hv) (hx ▸ h)
  exact ⟨hres,hrem.2.2,hspoke,hrem.2.1⟩
end Oberwolfach
