module

public import Oberwolfach.LongOrderedEveryClassMatchingBeforeFailure

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_ordered_joint_failure_budget (χ:ℝ) (hχ:0<χ):
    ∃ε₀ ηEvent:ℝ,0<ε₀ ∧ ε₀<1 ∧ 0<ηEvent ∧
      6*(ε₀+6*ηEvent)≤χ ∧ 6*(ε₀+6*ηEvent)<1 := by
  let ε₀:ℝ:=min (χ/24) (1/48)
  let ηEvent:ℝ:=min (χ/288) (1/288)
  have he:0<ε₀:=lt_min (by positivity) (by norm_num)
  have hη:0<ηEvent:=lt_min (by positivity) (by norm_num)
  have heχ:ε₀≤χ/24:=min_le_left _ _
  have he1:ε₀≤1/48:=min_le_right _ _
  have hηχ:ηEvent≤χ/288:=min_le_left _ _
  have hη1:ηEvent≤1/288:=min_le_right _ _
  exact ⟨ε₀,ηEvent,he,by linarith,hη,by linarith,by linarith⟩
end Oberwolfach
