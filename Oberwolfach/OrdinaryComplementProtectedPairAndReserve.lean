module

public import Oberwolfach.OrdinaryProtectedPairExact
public import Oberwolfach.OrdinaryReservoirSurvivesComplement

@[expose] public section
/-! Coverage of required rim edges and forced spoke targets gives exact inner
    agreement and preserves the same reservoir in the actual remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_complement_protected_pair_and_reservoir {n q:ℕ}
    (Target Sample Reference Protect:SimpleGraph (Fin n)) (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Href:Fin n→Fin q→Prop) (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Old E:Fin q→Finset (Sym2 (Fin n)))
    (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hRef:Reference≤Sample) (hRefTarget:Reference≤Target) (hProtect:Protect≤Reference)
    (hInnerProtect:spanningRestriction Reference Inner≤Protect)
    (hA:A⊆ordinaryHostResources Reference Href)
    (hReserveProtect:ordinaryResourceRim Reference A≤Protect)
    (hRim:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→
      (Target\Protect).Adj (f u x) (f u y))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=Old u∪E u)
    (hcover:∀e∈(ordinaryProtectedRequired Target Sample Reference Inner).edgeFinset,∃u,e∈E u)
    (hAvoid:∀u x,¬Href (f u x) u)
    (hSpokeCover:∀u v,v∈ordinaryInnerSpokeTargets Inner Hubs Href u→∃x,f u x=v):
    let R:=Target\ordinaryEmbeddedComplements Fs C f
    let S:=fun v u=>v∉Set.range (f u);
    A⊆ordinaryHostResources R S ∧
    (∀v∈Inner,∀w∈Inner,(R.Adj v w↔Reference.Adj v w)) ∧
    (∀v∈Inner,∀u∈Hubs,(S v u↔Href v u)):=by
  intro R S
  have hEmb:ordinaryEmbeddedComplements Fs C f≤Target\Protect:=by
    apply iSup_le
    intro u x y hxy
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj (f u) _ _ _).mp hxy
    exact hRim u a b hab
  have hcover':ordinaryProtectedRequired Target Sample Reference Inner≤ordinaryEmbeddedComplements Fs C f:=
    ordinary_required_edges_covered_by_complements _ Fs C f Old E hpartition hcover
  have hp:=ordinary_protected_pair_exact Target Sample Reference Protect (ordinaryEmbeddedComplements Fs C f) Inner Hubs Href f
    hRef hRefTarget hProtect hInnerProtect hEmb hcover' hAvoid hSpokeCover
  refine ⟨?_,hp.1,hp.2⟩
  apply ordinary_protected_reservoir_survives_complement Reference Target Fs C f Href A hA
    (hReserveProtect.trans (hProtect.trans hRefTarget))
  · intro u x y hxy
    have hh:=hRim u x y hxy
    exact ⟨hh.1,fun hr=>hh.2 (hReserveProtect hr)⟩
  · exact hAvoid
end Oberwolfach
