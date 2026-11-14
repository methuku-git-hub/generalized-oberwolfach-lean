module

public import Oberwolfach.OrdinaryLocalCycles

@[expose] public section
/-! Local cycles depend on a conflict graph only through pairs inside their
common vertex domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

def ordinaryLocalConflictEquiv (Q F F':SimpleGraph V) (T:Finset V)
    (h:∀v∈T,∀w∈T,F.Adj v w↔F'.Adj v w):
    LocalOrdinaryCycle Q F T r ≃ LocalOrdinaryCycle Q F' T r where
  toFun C:=⟨C.val,C.property.1,by
    intro v hv w hw hf
    exact C.property.2 v hv w hw ((h v (C.property.1 v hv) w (C.property.1 w hw)).mpr hf)⟩
  invFun C:=⟨C.val,C.property.1,by
    intro v hv w hw hf
    exact C.property.2 v hv w hw ((h v (C.property.1 v hv) w (C.property.1 w hw)).mp hf)⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem ordinary_local_conflict_equiv_vertices (Q F F':SimpleGraph V) (T:Finset V)
    (h:∀v∈T,∀w∈T,F.Adj v w↔F'.Adj v w) (C:LocalOrdinaryCycle Q F T r):
    localOrdinaryVertices (ordinaryLocalConflictEquiv Q F F' T h C)=localOrdinaryVertices C:=rfl
end Oberwolfach
