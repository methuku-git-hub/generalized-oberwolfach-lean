module

public import Oberwolfach.ResidualSelectedRunMarkerInterior
public import Oberwolfach.ResidualRunMarkerEquivalence

@[expose] public section
/-! The combinatorial surviving-marker count agrees with deleting the
interiors of the actual selected run subpaths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def selectedRunInteriors {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (c d:ℕ) (T:Finset ℕ) (hT:T⊆Finset.range d):Finset V :=
  (selectedSegmentRuns d T).attach.biUnion (fun r=>
    (selectedRunWalk p c r.1.1 r.1.2 ((selected_run_mem d T hT r.1.1 r.1.2).mp r.2).1).support.toFinset \
      {p.getVert (2+c*r.1.1),p.getVert (2+c*(r.1.2+1))})

theorem selected_marker_survival_iff {F:SimpleGraph V} {u v:V}
    (p:F.Walk u v) (hp:p.IsPath) (c d:ℕ) (hc:0<c)
    (hlen:p.length=c*d+4) (T:Finset ℕ) (hT:T⊆Finset.range d)
    (j:ℕ) (hj:j≤d):
    p.getVert (2+c*j)∉selectedRunInteriors p c d T hT ↔
      j∈survivingSegmentMarkers d T := by
  rw [surviving_segment_marker_iff_avoids_runs d T hT j]
  constructor
  · intro h
    refine ⟨hj,?_⟩
    intro a b hab hmid
    let r : {r // r∈selectedSegmentRuns d T}:=⟨(a,b),hab⟩
    have hr: IsSelectedSegmentRun T a b := (selected_run_mem d T hT a b).mp hab
    have hbT:b∈T := hr.2.1 b hr.1 le_rfl
    have hbd:b<d := by have hh:=hT hbT;simpa using hh
    apply h
    apply Finset.mem_biUnion.mpr
    refine ⟨r,by simp,?_⟩
    exact (selected_run_marker_interior_iff p hp c d a b j hc hr.1 hbd hj hlen).2 hmid
  · rintro ⟨_,h⟩ hmem
    obtain ⟨r,_,hrmem⟩:=Finset.mem_biUnion.mp hmem
    rcases r with ⟨⟨a,b⟩,hab⟩
    have hr: IsSelectedSegmentRun T a b := (selected_run_mem d T hT a b).mp hab
    have hbT:b∈T := hr.2.1 b hr.1 le_rfl
    have hbd:b<d := by have hh:=hT hbT;simpa using hh
    have hmid: a<j ∧ j≤b := (selected_run_marker_interior_iff p hp c d a b j hc hr.1 hbd hj hlen).1 hrmem
    exact h a b hab hmid
end Oberwolfach
