module

public import Oberwolfach.LongResidualRimComplementAvoidance

@[expose] public section
/-! An exact physical split identifies each complement image as part of the
small graph built from the same family of oriented arcs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_complement_image_in_small
    {U V:Type} [Fintype U] [DecidableEq U] [DecidableEq V]
    {X:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (F:∀u,SimpleGraph (X u)) (f:∀u,X u→V)
    (arcs:U→Finset (V×V)) (A:Finset (V×V)) (Small:SimpleGraph V) [Fintype V]
    (hA:A=Finset.univ.biUnion arcs)
    (hSmall:Small.edgeFinset=A.image (fun a=>s(a.1,a.2)))
    (hExact:∀u,((F u).edgeFinset.image (Sym2.map (f u)))=
      (arcs u).image (fun a=>s(a.1,a.2))):
    ∀u,((F u).edgeFinset.image (Sym2.map (f u)))⊆Small.edgeFinset:=by
  intro u e he
  rw [hExact u] at he
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he
  rw [hSmall,hA]
  exact Finset.mem_image.mpr ⟨a,Finset.mem_biUnion.mpr ⟨u,Finset.mem_univ _,ha⟩,rfl⟩
end Oberwolfach
