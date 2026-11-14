module

public import Oberwolfach.DirectedBoundarySupportEvent
public import Oberwolfach.BoundaryLabelChanges

@[expose] public section

/-! Auxiliary incidence degrees of the actual changed edges control both
boundary-support losses. The later mask may depend on the entire sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A W E:Type*} [Fintype A] [Fintype W] [Fintype E]
  [DecidableEq A] [DecidableEq W] [DecidableEq E]

theorem boundaryOutside_incident (tail head:A→W) (X:Finset W) (a:DirectedBoundaryEdge tail head X):
    tail a.val=boundaryOutside tail head X a∨head a.val=boundaryOutside tail head X a := by
  by_cases h:tail a.val∈X <;> simp [boundaryOutside,h]

theorem boundaryInside_incident (tail head:A→W) (X:Finset W) (a:DirectedBoundaryEdge tail head X):
    tail a.val=boundaryInside tail head X a∨head a.val=boundaryInside tail head X a := by
  by_cases h:tail a.val∈X <;> simp [boundaryInside,h]

theorem boundary_incident_change_count (tail head:A→W) (coin:A→E) (X:Finset W)
    (f:DirectedBoundaryEdge tail head X→W)
    (hf:∀ a,tail a.val=f a∨head a.val=f a) (σ τ:E→Bool) (x:W):
    (Finset.univ.filter (fun a:DirectedBoundaryEdge tail head X=>f a=x∧σ (coin a.val)≠τ (coin a.val))).card≤
      (Finset.univ.filter (fun a:A=>(tail a=x∨head a=x)∧σ (coin a)≠τ (coin a))).card := by
  have hs:(Finset.univ.filter (fun a:DirectedBoundaryEdge tail head X=>f a=x∧σ (coin a.val)≠τ (coin a.val))).image Subtype.val⊆
      Finset.univ.filter (fun a:A=>(tail a=x∨head a=x)∧σ (coin a)≠τ (coin a)) := by
    intro a ha
    obtain ⟨b,hb,he⟩:=Finset.mem_image.mp ha
    rw [←he]
    have hh:=(Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1 ▸ hf b,hh.2⟩
  have hh:=Finset.card_le_card hs
  simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using hh

theorem directed_boundary_support_changes (tail head:A→W) (coin:A↪E) (X:Finset W)
    (π:Equiv.Perm W) (σ τ:E→Bool) (L:ℝ)
    (hD:∀ x,((Finset.univ.filter (fun a:DirectedBoundaryEdge tail head X=>
      (tail a.val=x∨head a.val=x)∧σ (coin a.val)≠τ (coin a.val))).card:ℝ)≤L):
    (∀ x,((changed (directedBoundarySupport tail head coin X π σ x)
      (directedBoundarySupport tail head coin X π τ x)).card:ℝ)≤2*L)∧
    (∀ v,((changed
      (Finset.univ.filter (fun x=>v∈directedBoundarySupport tail head coin X π σ x))
      (Finset.univ.filter (fun x=>v∈directedBoundarySupport tail head coin X π τ x))).card:ℝ)≤2*L) := by
  let c:DirectedBoundaryEdge tail head X↪E:=(Function.Embedding.subtype _).trans coin
  let o:=boundaryOutside tail head X
  let a:=boundaryInside tail head X
  have hcount (f:DirectedBoundaryEdge tail head X→W)
      (hf:∀ z,tail z.val=f z∨head z.val=f z) (x:W):
      ((Finset.univ.filter (fun z=>f z=x∧σ (c z)≠τ (c z))).card:ℝ)≤L := by
    apply (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (hD x)
    intro z hz
    have hh:=(Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.1 ▸ hf z,hh.2⟩
  have ho (x:W):((Finset.univ.filter (fun z=>o z=x∧σ (c z)≠τ (c z))).card:ℝ)≤L :=
    hcount o (boundaryOutside_incident tail head X) x
  have ha (x:W):((Finset.univ.filter (fun z=>a z=x∧σ (c z)≠τ (c z))).card:ℝ)≤L :=
    hcount a (boundaryInside_incident tail head X) x
  simp only [directedBoundarySupport_incidence]
  refine ⟨?_,?_⟩
  · intro x
    have hh:=boundary_label_row_changes c o a π σ τ x
    have hh':((changed (retainedIncidenceSet (boundaryLabelCoordinates c o a π) σ x)
        (retainedIncidenceSet (boundaryLabelCoordinates c o a π) τ x)).card:ℝ)≤
        2*(Finset.univ.filter (fun z=>o z=x∧σ (c z)≠τ (c z))).card:=by exact_mod_cast hh
    exact hh'.trans (mul_le_mul_of_nonneg_left (ho x) (by norm_num))
  · intro v
    have hh:=boundary_label_membership_changes c o a π σ τ v
    have hh':((changed
        (Finset.univ.filter (fun x=>v∈retainedIncidenceSet (boundaryLabelCoordinates c o a π) σ x))
        (Finset.univ.filter (fun x=>v∈retainedIncidenceSet (boundaryLabelCoordinates c o a π) τ x))).card:ℝ)≤
      (Finset.univ.filter (fun z=>a z=v∧σ (c z)≠τ (c z))).card+
      (Finset.univ.filter (fun z=>a z=π.symm v∧σ (c z)≠τ (c z))).card:=by exact_mod_cast hh
    exact hh'.trans (by linarith [ha v,ha (π.symm v)])

end Oberwolfach
