module

public import Oberwolfach.MarkedIntervalBoundaryIdentity

@[expose] public section
/-! A permutation maps the complement of path interiors from the final-end
side to the initial-end side when the two boundary partitions agree. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem permutation_maps_path_complement
    {X:Type*} [Fintype X] [DecidableEq X]
    (σ:Equiv.Perm X) (A Y B T:Finset X)
    (hA:Y∪B=A) (hshift:Y∪B=Y.image σ∪T)
    (hYB:Disjoint Y B) (hYT:Disjoint (Y.image σ) T):
    ((Finset.univ\A)∪B).image σ=(Finset.univ\A)∪T:=by
  classical
  have himage (S:Finset X) (x:X):x∈S.image σ↔σ.symm x∈S:=by
    constructor
    · intro h
      obtain ⟨z,hz,hzx⟩:=Finset.mem_image.mp h
      rw [←hzx,Equiv.symm_apply_apply]
      exact hz
    · intro h
      exact Finset.mem_image.mpr ⟨σ.symm x,h,σ.apply_symm_apply x⟩
  have ha (x:X):x∈A↔x∈Y∨x∈B:=by rw [←hA,Finset.mem_union]
  have hb (x:X):x∈A↔x∈Y.image σ∨x∈T:=by rw [←hA,hshift,Finset.mem_union]
  ext x
  rw [himage]
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
  have he:=himage Y x
  have hd1:¬(σ.symm x∈Y ∧ σ.symm x∈B):=fun h=>Finset.disjoint_left.mp hYB h.1 h.2
  have hd2:¬(x∈Y.image σ ∧ x∈T):=fun h=>Finset.disjoint_left.mp hYT h.1 h.2
  have h1:=ha (σ.symm x)
  have h2:=hb x
  tauto
end Oberwolfach
