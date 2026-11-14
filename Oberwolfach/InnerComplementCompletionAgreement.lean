module

public import Oberwolfach.InnerResidualSpokeByComplementBounds
public import Oberwolfach.InnerProtectedCompletionImage
public import Oberwolfach.InnerProtectedTargetsCoverage

@[expose] public section
/-! The physical complement may omit path endpoints.  With the endpoint
bounds, protected completion still gives exact first-inner spoke agreement. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem inner_complement_completion_agreement
    (I:Finset V) (J:Finset U) (X:U→Type) [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (Y Old End Outer Outside R Absorber L Prescribed:U→Finset V)
    (B:∀u,Finset (X u)) (Φ g:∀u,X u→V)
    (hR:∀u,R u=Finset.univ\(Outside u∪End u))
    (hOutside:∀u,Outside u⊆Old u∪Finset.univ.image (Φ u))
    (hOldBound:∀u,Old u⊆Y u∪(Outside u∪End u))
    (hNewBound:∀u,Finset.univ.image (Φ u)⊆Y u∪(Outside u∪End u))
    (hOuterY:∀u,Disjoint (Outer u) (Y u))
    (hOuterOld:∀u,Disjoint (Outer u) (Old u))
    (hOuterEnd:∀u,Disjoint (Outer u) (End u))
    (hAbs:∀u∈J,Disjoint (Absorber u) I)
    (hB:∀u,(B u).image (g u)=Prescribed u∪innerRequiredTargets J I Outer Y Absorber Old u)
    (hag:∀u x,x∈B u→Φ u x=g u x)
    (hfree:∀u x,x∉B u→Φ u x∈L u)
    (hLI:∀u,Disjoint (L u) I)
    (hPO:∀u∈J,Disjoint (Prescribed u) (Outer u)):
    ∀u∈J,∀v∈I,(v∈R u\Y u↔v∈Outer u):=by
  have hNew:∀u,innerRequiredTargets J I Outer Y Absorber Old u⊆Finset.univ.image (Φ u):=by
    intro u v hv
    have hm:v∈(B u).image (g u):=by rw [hB u]; exact Finset.mem_union_right _ hv
    obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hm
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,(hag u x hx).trans hxv⟩
  obtain ⟨hTO,hcover⟩:=inner_protected_targets_coverage I J Outer Y Absorber Old
    (fun u=>Finset.univ.image (Φ u)) hAbs hNew
  apply inner_residual_spoke_by_complement_bounds I J Y Old (fun u=>Finset.univ.image (Φ u)) End Outer Outside R
    hR hOutside hOuterY hOuterOld hOuterEnd
  · intro u hu v hv hold
    exact Finset.mem_union.mp (hOldBound u hold)
  · intro u hu v hv ho
    exact inner_protected_completion_image_avoids I (L u) (Outer u) (Prescribed u)
      (innerRequiredTargets J I Outer Y Absorber Old u) (B u) (Φ u) (g u)
      (hB u) (hag u) (hfree u) (hLI u) (hPO u hu) (hTO u) v hv ho
  · intro u hu v hv ho hy hold
    have hm:=hNewBound u (hcover u hu v hv ho hy hold)
    rcases Finset.mem_union.mp hm with hY|hOther
    · exact False.elim (hy hY)
    · exact hOther
end Oberwolfach
