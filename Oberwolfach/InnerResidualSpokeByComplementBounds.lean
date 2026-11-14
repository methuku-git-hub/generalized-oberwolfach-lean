module

public import Oberwolfach.InnerRequiredTargets

@[expose] public section
/-! Equality on the inner pair only needs upper and lower information on the
actual complement image; that image need not equal the entire old or new image. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V]

theorem inner_residual_spoke_by_complement_bounds
    (I:Finset V) (J:Finset U) (Y Old New End Outer Outside R:U→Finset V)
    (hR:∀u,R u=Finset.univ\(Outside u∪End u))
    (hOutside:∀u,Outside u⊆Old u∪New u)
    (hOuterY:∀u,Disjoint (Outer u) (Y u))
    (hOuterOld:∀u,Disjoint (Outer u) (Old u))
    (hOuterEnd:∀u,Disjoint (Outer u) (End u))
    (hOldCover:∀u∈J,∀v∈I,v∈Old u→v∈Y u∨v∈Outside u∪End u)
    (hOuterNew:∀u∈J,∀v∈I,v∈Outer u→v∉New u)
    (hcover:∀u∈J,∀v∈I,v∉Outer u→v∉Y u→v∉Old u→v∈Outside u∪End u):
    ∀u∈J,∀v∈I,(v∈R u\Y u↔v∈Outer u):=by
  intro u hu v hv
  constructor
  · intro hr
    have hRmem: v∈R u:=(Finset.mem_sdiff.mp hr).1
    have hY:v∉Y u:=(Finset.mem_sdiff.mp hr).2
    rw [hR u] at hRmem
    have hNo: v∉Outside u∪End u:=(Finset.mem_sdiff.mp hRmem).2
    by_contra houter
    by_cases hold:v∈Old u
    · rcases hOldCover u hu v hv hold with hy|hx
      · exact hY hy
      · exact hNo hx
    · exact hNo (hcover u hu v hv houter hY hold)
  · intro ho
    apply Finset.mem_sdiff.mpr
    refine ⟨?_,(Finset.disjoint_left.mp (hOuterY u)) ho⟩
    rw [hR u]
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro hm
    rcases Finset.mem_union.mp hm with hout|hend
    · rcases Finset.mem_union.mp (hOutside u hout) with hold|hnew
      · exact (Finset.disjoint_left.mp (hOuterOld u)) ho hold
      · exact hOuterNew u hu v hv ho hnew
    · exact (Finset.disjoint_left.mp (hOuterEnd u)) ho hend
end Oberwolfach
