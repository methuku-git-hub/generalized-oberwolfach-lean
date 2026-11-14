module

public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The extended level zero is the full original vertex and hub domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε m)

def markedVortexInitialExtendedVertexEquiv:markedVortexVertexType Q 0≃V where
  toFun x:=x.val
  invFun x:=⟨x,by rw [Q.extendedVertices_eq (by omega),Q.initial];simp⟩
  left_inv x:=Subtype.ext rfl
  right_inv _:=rfl

def markedVortexInitialExtendedHubEquiv:markedVortexHubType Q 0≃U where
  toFun x:=x.val
  invFun x:=⟨x,by rw [Q.extendedIndices_eq (by omega),Q.indices_initial];simp⟩
  left_inv x:=Subtype.ext rfl
  right_inv _:=rfl

theorem marked_vortex_initial_extended_equiv_commutes
    (π:Equiv.Perm V) (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (x:markedVortexVertexType Q 0):
    markedVortexInitialExtendedVertexEquiv Q (markedVortexPermutation Q π hpres 0 x)=
      π (markedVortexInitialExtendedVertexEquiv Q x):=rfl
end Oberwolfach
