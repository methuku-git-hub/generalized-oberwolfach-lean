module

public import Oberwolfach.MarkedPackingHubArcCoverage
public import Oberwolfach.MarkedPhysicalHostGraph

@[expose] public section
/-! An injective physical edge map upgrades full physical rim coverage
to coverage of every ordered physical rim arc. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_packing_full_arc_coverage
    {V U E K:Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}
    (P:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (hphysical:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hRim:P.biUnion (fun W=>markedCyclePhysicalEdges tail head ktail khead m π b W.1)=
      markedPhysicalRimSet tail head ktail khead π):
    P.biUnion (fun W=>markedCyclePhysicalArcs tail head ktail khead m π b W.1)=
      Finset.univ.image (markedPhysicalArc tail head ktail khead π) := by
  ext x
  simp only [Finset.mem_biUnion,markedCyclePhysicalArcs,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨W,hW,i,hi⟩
    exact ⟨markedCycleTypedEdge tail head ktail khead m π b W.1 i,hi⟩
  · rintro ⟨e,he⟩
    have heRim:markedPhysicalEdge tail head ktail khead π e∈markedPhysicalRimSet tail head ktail khead π:=
      Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩
    rw [←hRim] at heRim
    obtain ⟨W,hW,hWedge⟩:=Finset.mem_biUnion.mp heRim
    unfold markedCyclePhysicalEdges at hWedge
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hWedge
    have hindex:markedCycleTypedEdge tail head ktail khead m π b W.1 i=e:=hphysical hi
    refine ⟨W,hW,i,?_⟩
    simpa [hindex] using he
end Oberwolfach
