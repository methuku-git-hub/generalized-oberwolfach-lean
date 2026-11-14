module

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

theorem ordinary_forbidden_complement_local_pair_and_absorber {n q:ℕ}
    (Target Sample Reference Protect Bad:SimpleGraph (Fin n)) (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Href:Fin n→Fin q→Prop) (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Old New:Fin q→Finset (Sym2 (Fin n))) (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hRef:Reference≤Sample)
    (hAgreement:∀v∈Inner,∀w∈Inner,Target.Adj v w↔Sample.Adj v w)
    (hProtect:Protect≤Reference) (hInnerProtect:spanningRestriction Reference Inner≤Protect)
    (hA:A⊆ordinaryHostResources Reference Href)
    (hReserveProtect:ordinaryResourceRim Reference A≤Protect)
    (hReserveTarget:ordinaryResourceRim Reference A≤Target)
    (hRim:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→
      (Target\Protect).Adj (f u x) (f u y))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=Old u∪New u)
    (hcover:∀e∈(ordinaryForbiddenRequired Target Sample Reference Bad Inner).edgeFinset,∃u,e∈New u)
    (hAvoidLocal:∀u,u∈Hubs→∀x,f u x∈Inner→¬Href (f u x) u)
    (hAvoidAbs:∀u x,f u x∉ordinaryReservoirSpokeLabels A u)
    (hSpokeCover:∀u v,v∈ordinaryInnerSpokeTargets Inner Hubs Href u→∃x,f u x=v):
    let R:=Target\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u);
    A⊆ordinaryHostResources R H ∧
    (∀v∈Inner,∀w∈Inner,(R.Adj v w↔Reference.Adj v w)) ∧
    (∀v∈Inner,∀u∈Hubs,(H v u↔Href v u)) ∧ Disjoint R Bad :=by
  intro R H
  have hEmb:ordinaryEmbeddedComplements Fs C f≤Target\Protect:=by
    apply iSup_le
    intro u x y hxy
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj (f u) _ _ _).mp hxy
    exact hRim u a b hab
  have hcover':∀e∈(ordinaryProtectedRequired Target Sample Reference Inner).edgeFinset,∃u,e∈New u:=by
    intro e he
    apply hcover e
    exact SimpleGraph.edgeFinset_mono (show ordinaryProtectedRequired Target Sample Reference Inner≤
      ordinaryForbiddenRequired Target Sample Reference Bad Inner from le_sup_left) he
  have hcovered:ordinaryProtectedRequired Target Sample Reference Inner≤ordinaryEmbeddedComplements Fs C f:=
    ordinary_required_edges_covered_by_complements _ Fs C f Old New hpartition hcover'
  have hp:=ordinary_protected_pair_exact_with_local_spoke_avoidance Target Sample Reference Protect
    (ordinaryEmbeddedComplements Fs C f) Inner Hubs Href f hRef
    (ordinary_sample_reference_local_containment Target Sample Reference Inner hRef hAgreement)
    hProtect hInnerProtect hEmb hcovered hAvoidLocal hSpokeCover
  have hres:=ordinary_protected_reservoir_survives_actual_label_avoidance Reference Target Fs C f Href A hA hReserveTarget
    (by
      intro u x y hxy
      have hh:=hRim u x y hxy
      exact ⟨hh.1,fun hr=>hh.2 (hReserveProtect hr)⟩) hAvoidAbs
  have hf:=ordinary_forbidden_placement_completion_inputs Target Sample Reference Bad Inner Fs C f Old New hpartition hcover
  exact ⟨hres,hp.1,hp.2,hf.2.1⟩
end Oberwolfach
