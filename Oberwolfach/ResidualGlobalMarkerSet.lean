module

public import Oberwolfach.ResidualGlobalMarkerSurvival

@[expose] public section
/-! Identify the manuscript's surviving selected-path marker set with the
per-path surviving marker indices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem selected_marker_global_set_identity (F:SimpleGraph V)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:0<c) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i,T i⊆Finset.range d) (C:Finset V)
    (hC:∀i∈s₁∪s₂,Disjoint (P i).support.toFinset C):
    let R:=Finset.univ \ (C ∪ (s₁∪s₂).biUnion (pathFamilyLocalDeletion F s₁ u v P c d T hT));
    R ∩ s₂.biUnion (fun i=>(Finset.range (d+1)).image (fun j=>(P i).getVert (2+c*j))) =
      s₂.biUnion (fun i=>(survivingSegmentMarkers d (T i)).image (fun j=>(P i).getVert (2+c*j))) := by
  dsimp only
  ext x
  constructor
  · intro hx
    have hx':=Finset.mem_inter.mp hx
    have hsurv: x∉C ∪ (s₁∪s₂).biUnion (pathFamilyLocalDeletion F s₁ u v P c d T hT) :=
      (Finset.mem_sdiff.mp hx'.1).2
    obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hx'.2
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx
    have hjd:j≤d := by simpa using hj
    have hm: j∈survivingSegmentMarkers d (T i) :=
      (selected_marker_survives_global_deletion F s₁ s₂ hs u v P hp hP c d hc hlen T hT C hC i hi j hjd).1 hsurv
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_image.mpr ⟨j,hm,rfl⟩⟩
  · intro hx
    obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx
    have hjr:j∈Finset.range (d+1) := (Finset.mem_sdiff.mp hj).1
    have hjd:j≤d := by simpa using hjr
    have hsurv := (selected_marker_survives_global_deletion F s₁ s₂ hs u v P hp hP c d hc hlen T hT C hC i hi j hjd).2 hj
    exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hsurv⟩,
      Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_image.mpr ⟨j,hjr,rfl⟩⟩⟩
end Oberwolfach
