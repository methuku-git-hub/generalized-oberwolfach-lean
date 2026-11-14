module

public import Oberwolfach.ReservedPairAllowedHubs

@[expose] public section
/-! For outer hubs, excluding inner vertices and the hub's absorber targets
preserves the eligible hubs for an edge outside the inner vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_pair_hubs_after_outer_exclusions
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (Lists:U→Finset V) (inner:Finset U) (I:Finset V) (Z:U→Finset V) (x y:V)
    (hx:x∉I) (hy:y∉I) (hZ:∀u,u∉inner→Z u=∅):
    protectedPairEdgeHubs (fun u=>Lists u\(I∪Z u)) inner s(x,y)=
      protectedPairEdgeHubs Lists inner s(x,y):=by
  ext u
  simp only [protectedPairEdgeHubs,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hu,he⟩
    refine ⟨hu,?_⟩
    intro v hv
    exact (Finset.mem_sdiff.mp (he v hv)).1
  · rintro ⟨hu,he⟩
    refine ⟨hu,?_⟩
    intro v hv
    have hv':v=x∨v=y:=by simpa [Sym2.toFinset_mk_eq] using hv
    apply Finset.mem_sdiff.mpr
    refine ⟨he v hv,?_⟩
    rw [hZ u hu]
    simp only [Finset.union_empty]
    rcases hv' with rfl|rfl <;> assumption
end Oberwolfach
