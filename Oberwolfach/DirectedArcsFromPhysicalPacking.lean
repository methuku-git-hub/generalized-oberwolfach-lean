module

public import Oberwolfach.PrescribedEmbeddingDisjointUpdate

@[expose] public section
/-! Physical-edge disjointness of the existing factor packing implies
pairwise disjointness of directed arc families contained in it. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem directed_arcs_disjoint_of_physical_packing
    {V U:Type*} [DecidableEq V] (D:U→Finset (V×V)) (E:U→Finset (Sym2 V))
    (hcontain:∀w,(D w).image (fun p=>s(p.1,p.2))⊆E w)
    (hpair:∀w z,w≠z→Disjoint (E w) (E z)):
    ∀w z,w≠z→Disjoint (D w) (D z):=by
  intro w z hwz
  apply Finset.disjoint_left.mpr
  intro a haw haz
  have hw:s(a.1,a.2)∈E w:=hcontain w (Finset.mem_image.mpr ⟨a,haw,rfl⟩)
  have hz:s(a.1,a.2)∈E z:=hcontain z (Finset.mem_image.mpr ⟨a,haz,rfl⟩)
  exact Finset.disjoint_left.mp (hpair w z hwz) hw hz
end Oberwolfach
