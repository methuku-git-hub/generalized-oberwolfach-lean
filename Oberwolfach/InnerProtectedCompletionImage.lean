module

public import Oberwolfach.InnerRequiredTargetsProtectedMonotone

@[expose] public section
/-! A protected inner spoke cannot be consumed by a completion whose free
images avoid the inner vertices and whose prescribed images and targets
avoid that spoke. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V X:Type} [Fintype X] [DecidableEq X] [DecidableEq V]

theorem inner_protected_completion_image_avoids
    (I L Outer Prescribed Target:Finset V) (B:Finset X) (Φ g:X→V)
    (hB:(B.image g)=Prescribed∪Target)
    (hag:∀x∈B,Φ x=g x) (hfree:∀x,x∉B→Φ x∈L)
    (hLI:Disjoint L I) (hPO:Disjoint Prescribed Outer) (hTO:Disjoint Target Outer):
    ∀v∈I,v∈Outer→v∉Finset.univ.image Φ:=by
  intro v hvI hvO himage
  obtain ⟨x,_,hx⟩:=Finset.mem_image.mp himage
  by_cases hb:x∈B
  · have hh:Φ x∈Prescribed∪Target:=by
      rw [←hB]
      exact Finset.mem_image.mpr ⟨x,hb,(hag x hb).symm⟩
    rw [hx] at hh
    rcases Finset.mem_union.mp hh with hp|ht
    · exact (Finset.disjoint_left.mp hPO) hp hvO
    · exact (Finset.disjoint_left.mp hTO) ht hvO
  · have hh:=hfree x hb
    rw [hx] at hh
    exact (Finset.disjoint_left.mp hLI) hh hvI
end Oberwolfach
