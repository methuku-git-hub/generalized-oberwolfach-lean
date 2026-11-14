module

public import Oberwolfach.ResidualActualReindex

@[expose] public section
/-! Reindexing selected cycles preserves the vertices already embedded. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V K J J' : Type} [Fintype V] [DecidableEq V] [DecidableEq K]
  [DecidableEq J] [DecidableEq J'] {F : SimpleGraph V}

theorem ActualResidualData.reindexCycles_prescribed
    (a : ActualResidualData (K:=K) (J:=J) F) (e : J' ≃ J) :
    (a.reindexCycles e).prescribed = a.prescribed := by
  unfold prescribed
  rw [ActualResidualData.reindexCycles_remaining]
  rfl

theorem ActualResidualData.reindexCycles_oldDomain
    (a : ActualResidualData (K:=K) (J:=J) F) (e : J' ≃ J) :
    (a.reindexCycles e).oldDomain = a.oldDomain := by
  unfold oldDomain
  rw [ActualResidualData.reindexCycles_prescribed]
  rfl
end Oberwolfach
