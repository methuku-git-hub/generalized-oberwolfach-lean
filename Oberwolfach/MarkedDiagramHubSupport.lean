module

public import Oberwolfach.MarkedInitialDiagramIdentity

@[expose] public section

/-! Explicit hub support for the actual initial packing. Hub switches use
only the old source and image hubs and introduce no further hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}
    {src dst:A→V} {row:S→V} {φ:V→V} {u u':S→U} {jr:A→Bool} {js:S→Bool}
    {W Z:Finset V} {B:Finset U}

def markedDiagramHubs (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):Finset U:=
  (Finset.univ.image u∪Finset.univ.image u')∪Finset.univ.image D.hub

theorem marked_diagram_hubs_card
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):
    (markedDiagramHubs D).card≤2*Fintype.card S+Fintype.card A:=by
  have h₁:(Finset.univ.image u).card≤Fintype.card S:=by simpa using Finset.card_image_le (f:=u) (s:=Finset.univ)
  have h₂:(Finset.univ.image u').card≤Fintype.card S:=by simpa using Finset.card_image_le (f:=u') (s:=Finset.univ)
  have h₃:(Finset.univ.image D.hub).card≤Fintype.card A:=by simpa using Finset.card_image_le (f:=D.hub) (s:=Finset.univ)
  have hu:=Finset.card_union_le (Finset.univ.image u) (Finset.univ.image u')
  have hv:=Finset.card_union_le (Finset.univ.image u∪Finset.univ.image u') (Finset.univ.image D.hub)
  unfold markedDiagramHubs
  omega

theorem marked_diagram_plus_hubs
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):
    ∀ v z,Sum.inr (v,z)∈markedDiagramPlus D→z∈markedDiagramHubs D:=by
  intro v z he
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
  rcases i with a|(s|a)
  · have hz:=((markedWheelPhysicalResources_spoke (D.RC a) v z).mp hi).1
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,(D.rimHubs a).1.symm.trans hz⟩)
  · have hz:=((markedWheelPhysicalResources_spoke (D.SC s) v z).mp hi).1
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s,Finset.mem_univ _,(D.spokeHubs s).1.symm.trans hz⟩))
  · have hz:=((markedWheelPhysicalResources_spoke (D.VD a) v z).mp hi).1
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,Finset.mem_univ _,(D.vertexHubs a).2.symm.trans hz⟩)

theorem marked_diagram_hubs_old
    (D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B):
    ∀ z∈markedDiagramHubs D,z∈B→∃ a:S,u a=z∨u' a=z:=by
  intro z hz hzB
  rcases Finset.mem_union.mp hz with hz|hz
  · rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hz;exact ⟨a,Or.inl ha⟩
    · obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hz;exact ⟨a,Or.inr ha⟩
  · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp hz
    exact (D.freshHub a hzB).elim

end Oberwolfach
