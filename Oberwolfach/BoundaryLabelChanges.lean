module

public import Oberwolfach.BoundaryLabelCoordinates
public import Oberwolfach.Neighbourhoods

@[expose] public section

/-! A changed boundary support is witnessed by an actual changed physical
coordinate. These deterministic bounds apply to later adaptive masks and
are not multiplied by the original retention probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A J V E:Type*} [Fintype A] [Fintype J] [Fintype V] [Fintype E]
  [DecidableEq A] [DecidableEq J] [DecidableEq V] [DecidableEq E]

theorem boundary_label_changed_witness (coin:A↪E) (owner:A→J) (label:A→V) (π:Equiv.Perm V)
    (σ τ:E→Bool) (j:J) (v:V)
    (hv:v∈changed
      (retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) σ j)
      (retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) τ j)):
    ∃ a,owner a=j∧(label a=v∨π (label a)=v)∧σ (coin a)≠τ (coin a) := by
  have hdir (σ τ:E→Bool)
      (hs:v∈retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) σ j)
      (ht:v∉retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) τ j):
      ∃ a,owner a=j∧(label a=v∨π (label a)=v)∧σ (coin a)≠τ (coin a) := by
    obtain ⟨e,he,hσ⟩:=(mem_retainedIncidenceSet _ _ _ _).mp hs
    obtain ⟨a,ha,hl,hea⟩:=(boundaryLabelCoordinates_mem coin owner label π j v e).mp he
    refine ⟨a,ha,hl,?_⟩
    intro hst
    apply ht
    apply (mem_retainedIncidenceSet _ _ _ _).mpr
    refine ⟨e,he,?_⟩
    rw [←hea,←hst,hea]
    exact hσ
  rcases (show (v∈retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) σ j∧
      v∉retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) τ j)∨
      (v∈retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) τ j∧
      v∉retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) σ j) from by
      simpa only [changed,Finset.mem_union,Finset.mem_sdiff] using hv) with h|h
  · exact hdir σ τ h.1 h.2
  · obtain ⟨a,ha,hl,hst⟩:=hdir τ σ h.1 h.2
    exact ⟨a,ha,hl,Ne.symm hst⟩

theorem boundary_label_row_changes (coin:A↪E) (owner:A→J) (label:A→V) (π:Equiv.Perm V)
    (σ τ:E→Bool) (j:J):
    (changed (retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) σ j)
      (retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) τ j)).card≤
      2*(Finset.univ.filter (fun a=>owner a=j∧σ (coin a)≠τ (coin a))).card := by
  let D:=Finset.univ.filter (fun a=>owner a=j∧σ (coin a)≠τ (coin a))
  have hs:changed (retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) σ j)
      (retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) τ j)⊆
      D.image label∪(D.image label).image π := by
    intro v hv
    obtain ⟨a,ha,hl,hd⟩:=boundary_label_changed_witness coin owner label π σ τ j v hv
    have haD:a∈D:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,hd⟩
    rcases hl with hl|hl
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,haD,hl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨label a,Finset.mem_image.mpr ⟨a,haD,rfl⟩,hl⟩)
  calc
    _ ≤ (D.image label∪(D.image label).image π).card:=Finset.card_le_card hs
    _ ≤ (D.image label).card+((D.image label).image π).card:=Finset.card_union_le _ _
    _ ≤ 2*D.card:=by have h₁:=Finset.card_image_le (s:=D) (f:=label);have h₂:=Finset.card_image_le (s:=D.image label) (f:=π);omega

theorem boundary_label_membership_changes (coin:A↪E) (owner:A→J) (label:A→V) (π:Equiv.Perm V)
    (σ τ:E→Bool) (v:V):
    (changed
      (Finset.univ.filter (fun j=>v∈retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) σ j))
      (Finset.univ.filter (fun j=>v∈retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) τ j))).card≤
      (Finset.univ.filter (fun a=>label a=v∧σ (coin a)≠τ (coin a))).card+
      (Finset.univ.filter (fun a=>label a=π.symm v∧σ (coin a)≠τ (coin a))).card := by
  let D:=fun w=>Finset.univ.filter (fun a=>label a=w∧σ (coin a)≠τ (coin a))
  have hs:changed
      (Finset.univ.filter (fun j=>v∈retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) σ j))
      (Finset.univ.filter (fun j=>v∈retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) τ j))⊆
      (D v∪D (π.symm v)).image owner := by
    intro j hj
    have hv:v∈changed (retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) σ j)
        (retainedIncidenceSet (boundaryLabelCoordinates coin owner label π) τ j) := by
      simpa only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and] using hj
    obtain ⟨a,ha,hl,hd⟩:=boundary_label_changed_witness coin owner label π σ τ j v hv
    refine Finset.mem_image.mpr ⟨a,?_,ha⟩
    rcases hl with hl|hl
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl,hd⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa using congrArg π.symm hl,hd⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_image_le.trans (Finset.card_union_le _ _))

end Oberwolfach
