module

public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The first vortex level is the original physical vertex and hub set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

def markedVortexLevelZeroVertexEquiv : markedVortexVertexType Q 0 ≃o V where
  toFun x:=x.val
  invFun x:=⟨x,by rw [Q.extendedVertices_eq (Nat.zero_le _),Q.initial];exact Finset.mem_univ _⟩
  left_inv x:=Subtype.ext rfl
  right_inv _:=rfl
  map_rel_iff':=by intro x y;rfl

def markedVortexLevelZeroHubEquiv : markedVortexHubType Q 0 ≃ U where
  toFun x:=x.val
  invFun x:=⟨x,by rw [Q.extendedIndices_eq (Nat.zero_le _),Q.indices_initial];exact Finset.mem_univ _⟩
  left_inv x:=Subtype.ext rfl
  right_inv _:=rfl

theorem marked_vortex_level_zero_physical_maps
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i):
    (∀ v,markedVortexLevelZeroVertexEquiv Q v=markedVortexVertexEmbedding Q 0 v) ∧
    (∀ u,markedVortexLevelZeroHubEquiv Q u=markedVortexHubEmbedding Q 0 u) ∧
    (∀ v,markedVortexLevelZeroVertexEquiv Q (markedVortexPermutation Q π hπ 0 v)=π (markedVortexLevelZeroVertexEquiv Q v)) ∧
    (Fintype.card (markedVortexVertexType Q 0)=Fintype.card V) ∧
    (Fintype.card (markedVortexHubType Q 0)=Fintype.card U) := by
  refine ⟨fun _=>rfl,fun _=>rfl,fun _=>rfl,?_,?_⟩
  · exact Fintype.card_congr (markedVortexLevelZeroVertexEquiv Q).toEquiv
  · exact Fintype.card_congr (markedVortexLevelZeroHubEquiv Q)
end Oberwolfach
