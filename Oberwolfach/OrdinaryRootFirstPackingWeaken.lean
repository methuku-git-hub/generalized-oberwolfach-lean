module

public import Oberwolfach.OrdinaryRootFirstPackingContext

@[expose] public section
/-! Relaxing the leftover threshold preserves the actual root cover,
boundary reserve and selected wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_packing_weaken
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t t':ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t) (h:t≤t'):
    ∃K':OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t',
      K'.cover=K.cover ∧ K'.reserve=K.reserve:=by
  let P:OrdinaryUnreservedPackingData _ _ _ _ _ _ r t':=
    ⟨K.packing.wheels,K.packing.disjoint,fun w=>(K.packing.leftover w).trans h⟩
  exact ⟨⟨K.root_sub,K.hub_sub,K.cover,K.reserve,P⟩,rfl,rfl⟩
end Oberwolfach
