module

public import Oberwolfach.InnerProtectedCompletionImage
public import Oberwolfach.InnerProtectedTargetsCoverage
public import Oberwolfach.InnerResidualSpokeExactAgreement

@[expose] public section
/-! Exact inner-pair spoke agreement from the actual completion's prescribed,
required and free images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem inner_protected_completion_exact_agreement
    (I:Finset V) (J:Finset U) (X:U→Type) [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (Y Old End Outer R Absorber L Prescribed:U→Finset V)
    (B:∀u,Finset (X u)) (Φ g:∀u,X u→V)
    (hR:∀u,R u=Finset.univ\(Old u∪Finset.univ.image (Φ u)∪End u))
    (hOuterY:∀u,Disjoint (Outer u) (Y u))
    (hOuterOld:∀u,Disjoint (Outer u) (Old u))
    (hOuterEnd:∀u,Disjoint (Outer u) (End u))
    (hAbs:∀u∈J,Disjoint (Absorber u) I)
    (hB:∀u,(B u).image (g u)=Prescribed u∪innerRequiredTargets J I Outer Y Absorber Old u)
    (hag:∀u x,x∈B u→Φ u x=g u x)
    (hfree:∀u x,x∉B u→Φ u x∈L u)
    (hLI:∀u,Disjoint (L u) I)
    (hPO:∀u,Disjoint (Prescribed u) (Outer u)):
    ∀u∈J,∀v∈I,(v∈R u\Y u↔v∈Outer u):=by
  have hNew:∀u,innerRequiredTargets J I Outer Y Absorber Old u⊆Finset.univ.image (Φ u):=by
    intro u v hv
    have hm:v∈(B u).image (g u):=by rw [hB u]; exact Finset.mem_union_right _ hv
    obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hm
    apply Finset.mem_image.mpr
    exact ⟨x,Finset.mem_univ _,(hag u x hx).trans hxv⟩
  obtain ⟨hTO,hcover⟩:=inner_protected_targets_coverage I J Outer Y Absorber Old
    (fun u=>Finset.univ.image (Φ u)) hAbs hNew
  apply inner_residual_spoke_exact_agreement I J Y Old (fun u=>Finset.univ.image (Φ u)) End Outer R
    hR hOuterY hOuterOld hOuterEnd
  · intro u hu v hv ho
    exact inner_protected_completion_image_avoids I (L u) (Outer u) (Prescribed u)
      (innerRequiredTargets J I Outer Y Absorber Old u) (B u) (Φ u) (g u)
      (hB u) (hag u) (hfree u) (hLI u) (hPO u) (hTO u) v hv ho
  · exact hcover
end Oberwolfach
