module

public import Oberwolfach.MarkedVortexRestrictionChain

@[expose] public section
/-! Exact identification of an inner parent domain with the next vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

def markedVortexInnerVertexEquiv (i:ℕ):
    markedVortexVertexType Q (i+1) ≃ ↥(markedVortexInnerVertices Q i) where
  toFun x:=⟨markedVortexNestedVertex Q i (i+1) (by omega) x,by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,x.property⟩⟩
  invFun x:=⟨x.val.val,(Finset.mem_filter.mp x.property).2⟩
  left_inv x:=by apply Subtype.ext;rfl
  right_inv x:=by apply Subtype.ext;apply Subtype.ext;rfl

def markedVortexInnerHubEquiv (i:ℕ):
    markedVortexHubType Q (i+1) ≃ ↥(markedVortexInnerHubs Q i) where
  toFun x:=⟨markedVortexNestedHub Q i (i+1) (by omega) x,by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,x.property⟩⟩
  invFun x:=⟨x.val.val,(Finset.mem_filter.mp x.property).2⟩
  left_inv x:=by apply Subtype.ext;rfl
  right_inv x:=by apply Subtype.ext;apply Subtype.ext;rfl

theorem marked_vortex_inner_vertex_equiv_nested (i:ℕ) (x:markedVortexVertexType Q (i+1)):
    (markedVortexInnerVertexEquiv Q i x).val=markedVortexNestedVertex Q i (i+1) (by omega) x:=rfl

theorem marked_vortex_inner_hub_equiv_nested (i:ℕ) (u:markedVortexHubType Q (i+1)):
    (markedVortexInnerHubEquiv Q i u).val=markedVortexNestedHub Q i (i+1) (by omega) u:=rfl
end Oberwolfach
