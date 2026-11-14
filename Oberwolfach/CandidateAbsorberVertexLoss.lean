module

public import Oberwolfach.CandidateResourceRestriction
public import Oberwolfach.AbsorberOccurrenceRoots
public import Oberwolfach.LabelledRecordDeletionCounts

@[expose] public section

/-! Vertex deletion from a candidate family on the same ambient vertex type.
Roots are retained and only free-label intersections contribute to the loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T] {c : ℕ}

theorem candidate_absorber_vertex_loss (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X Z : Finset V) (hXZ : Disjoint X Z)
    (J : ℕ) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y}≤J) :
    Fintype.card (LabelledAbsorberFamily R S X)≤
      Fintype.card (LabelledAbsorberFamily (candidateResourceSet R (fun C₀=>Disjoint (R C₀) Z)) S X)+
      Z.card*((c*c)*Fintype.card T*X.card^c*Fintype.card V^(c*c-1)*J^(2*c+1)) := by
  have hh := candidate_absorber_card_loss R (fun C₀=>Disjoint (R C₀) Z) S X
  have hb := labelled_absorber_free_deletion_count R S X Z J hJ
  have hbad : Fintype.card {D : LabelledAbsorberFamily R S X // ¬∀ o,Disjoint (R (D.2.2 o).val) Z}≤
      Fintype.card {D : LabelledAbsorberFamily R S X // ¬Disjoint (labelledAbsorberFree R (S D.1) X D.2) Z} := by
    apply Fintype.card_subtype_mono
    intro D hD hf
    apply hD
    intro o
    apply Finset.disjoint_left.mpr
    intro v hv hz
    have hs := labelled_absorber_occurrence_subset R (S D.1) X D.2 o hv
    rcases Finset.mem_union.mp hs with hv'|hv'
    · exact Finset.disjoint_left.mp hf hv' hz
    · exact Finset.disjoint_left.mp hXZ hv' hz
  exact hh.trans (Nat.add_le_add_left (hbad.trans hb) _)

end Oberwolfach
