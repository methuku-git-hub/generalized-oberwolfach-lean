module

public import Oberwolfach.PrescribedArcCount
public import Oberwolfach.PrescribedInducedEdgeRelabel
public import Oberwolfach.PrescribedPieceArcPhysical

@[expose] public section
/-! Passing from induced directed arcs to physical edge images preserves
exactly the prescribed edge set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_induced_physical_image (Q:SimpleGraph X) (D:X→X→Prop)
    (hrep:∀x y,Q.Adj x y→D x y ∨ D y x) (hDQ:∀x y,D x y→Q.Adj x y)
    (A:Finset X) (f:X→V):
    (prescribedInducedSourceEdges Q A).image (Sym2.map f)=
      ((prescribedInducedArcs D A).image (Prod.map f f)).image prescribedArcPhysical := by
  ext e
  constructor
  · intro he
    obtain ⟨a,ha,hae⟩:=Finset.mem_image.mp he
    induction a using Sym2.ind with
    | _ x y =>
      have hxy:Q.Adj x y ∧ x∈A ∧ y∈A:=(prescribed_induced_edge_mk Q A x y).mp ha
      rcases hrep x y hxy.1 with h|h
      · apply Finset.mem_image.mpr
        refine ⟨(f x,f y),?_,?_⟩
        · apply Finset.mem_image.mpr
          refine ⟨(x,y),?_,rfl⟩
          simp [prescribedInducedArcs,hxy.2.1,hxy.2.2,h]
        · simpa [prescribedArcPhysical] using hae
      · apply Finset.mem_image.mpr
        refine ⟨(f y,f x),?_,?_⟩
        · apply Finset.mem_image.mpr
          refine ⟨(y,x),?_,rfl⟩
          simp [prescribedInducedArcs,hxy.2.1,hxy.2.2,h]
        · simpa [prescribedArcPhysical,Sym2.eq_swap] using hae
  · intro he
    obtain ⟨e',he',heq⟩:=Finset.mem_image.mp he
    obtain ⟨a,ha,hae⟩:=Finset.mem_image.mp he'
    rcases a with ⟨x,y⟩
    have hh:x∈A ∧ y∈A ∧ D x y:=by simpa [prescribedInducedArcs] using ha
    apply Finset.mem_image.mpr
    refine ⟨s(x,y),(prescribed_induced_edge_mk Q A x y).mpr ⟨hDQ x y hh.2.2,hh.1,hh.2.1⟩,?_⟩
    subst e'
    simpa [prescribedArcPhysical] using heq
end Oberwolfach
