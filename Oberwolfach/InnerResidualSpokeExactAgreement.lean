module

public import Oberwolfach.InnerRequiredTargetsProtectedMonotone

@[expose] public section
/-! Set-theoretic endpoint of the protected completion: on the inner pair,
the ordinary residual equals the retained ordinary spoke set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V]

theorem inner_residual_spoke_exact_agreement
    (I:Finset V) (J:Finset U) (Y Old New End Outer R:U→Finset V)
    (hR:∀u,R u=Finset.univ\(Old u∪New u∪End u))
    (hOuterY:∀u,Disjoint (Outer u) (Y u))
    (hOuterOld:∀u,Disjoint (Outer u) (Old u))
    (hOuterEnd:∀u,Disjoint (Outer u) (End u))
    (hOuterNew:∀u∈J,∀v∈I,v∈Outer u→v∉New u)
    (hcover:∀u∈J,∀v∈I,v∉Outer u→v∉Y u→v∉Old u→v∈New u):
    ∀u∈J,∀v∈I,(v∈R u\Y u↔v∈Outer u):=by
  intro u hu v hv
  constructor
  · intro hr
    by_contra ho
    have hrR: v∈R u:=(Finset.mem_sdiff.mp hr).1
    have hrY: v∉Y u:=(Finset.mem_sdiff.mp hr).2
    have hnOld:v∉Old u:=by
      rw [hR u] at hrR
      exact fun h=> (Finset.mem_sdiff.mp hrR).2 (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hnNew:v∉New u:=by
      rw [hR u] at hrR
      exact fun h=> (Finset.mem_sdiff.mp hrR).2 (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    exact hnNew (hcover u hu v hv ho hrY hnOld)
  · intro ho
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [hR u]
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [Finset.mem_union,not_or]
      exact ⟨⟨(Finset.disjoint_left.mp (hOuterOld u)) ho,hOuterNew u hu v hv ho⟩,
        (Finset.disjoint_left.mp (hOuterEnd u)) ho⟩
    · exact (Finset.disjoint_left.mp (hOuterY u)) ho
end Oberwolfach
