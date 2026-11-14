module

public import Oberwolfach.ResidualSelectedMarkerSurvival
public import Oberwolfach.ResidualMarkerInjection
public import Oberwolfach.ResidualMaximalRunCounts

@[expose] public section
/-! Count the surviving physical markers of an actual extended source path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem selected_path_surviving_physical_markers (F:SimpleGraph V) {u v:V}
    (p:F.Walk u v) (hp:p.IsPath) (c d:ℕ) (hc:0<c)
    (hlen:p.length=c*d+4) (T:Finset ℕ) (hT:T⊆Finset.range d):
    ((Finset.range (d+1)).image (fun j=>p.getVert (2+c*j)) \
      selectedRunInteriors p c d T hT) =
      (survivingSegmentMarkers d T).image (fun j=>p.getVert (2+c*j)) := by
  ext x
  constructor
  · intro hx
    have hx':=Finset.mem_sdiff.mp hx
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx'.1
    have hjd:j≤d := by simpa using hj
    have hs: j∈survivingSegmentMarkers d T :=
      (selected_marker_survival_iff p hp c d hc hlen T hT j hjd).1 hx'.2
    exact Finset.mem_image.mpr ⟨j,hs,rfl⟩
  · intro hx
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx
    have hjr:j∈Finset.range (d+1) := (Finset.mem_sdiff.mp hj).1
    have hjd:j≤d := by simpa using hjr
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨j,hjr,rfl⟩,?_⟩
    exact (selected_marker_survival_iff p hp c d hc hlen T hT j hjd).2 hj

theorem selected_path_surviving_physical_marker_count (F:SimpleGraph V) {u v:V}
    (p:F.Walk u v) (hp:p.IsPath) (c d:ℕ) (hc:0<c) (hlen:p.length=c*d+4)
    (T:Finset ℕ) (hT:T⊆Finset.range d):
    ((Finset.range (d+1)).image (fun j=>p.getVert (2+c*j)) \
      selectedRunInteriors p c d T hT).card =
      1+(d-T.card)+(selectedSegmentRuns d T).card := by
  rw [selected_path_surviving_physical_markers F p hp c d hc hlen T hT]
  have hsub:survivingSegmentMarkers d T⊆Finset.range (d+1) := Finset.sdiff_subset
  rw [extended_path_marker_image_card p hp c d hc hlen _ hsub]
  have h:=selected_run_marker_count_exact d T hT
  rw [selected_segment_runs_card d T hT]
  exact h
end Oberwolfach
