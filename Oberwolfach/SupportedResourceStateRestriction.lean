module

public import Oberwolfach.ResourcePatternConcentration

@[expose] public section
/-! Filtering physical resources leaves a fixed-weight root load unchanged
when every nonzero-weight candidate uses only permitted resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B C:Type} [Fintype A] [Fintype C] [DecidableEq A]

def physicallyRestrictedState (φ:A→B) (eligible:B→Prop) (σ:A→Bool):A→Bool:=
  fun a=>if eligible (φ a) then σ a else false

theorem supported_resource_pattern_restrict_state
    (φ:A→B) (eligible:B→Prop) (R:C→Finset A) (w:C→ℝ) (σ:A→Bool)
    (hsupport:∀c,w c≠0→∀a∈R c,eligible (φ a)) (root:A):
    resourcePatternLoad R w (fun _ _=>true) root (physicallyRestrictedState φ eligible σ)=
      resourcePatternLoad R w (fun _ _=>true) root σ :=by
  unfold resourcePatternLoad
  apply Finset.sum_congr rfl
  intro c _
  by_cases hw:w c=0
  · simp [hw]
  · have hagree:∀a∈R c,physicallyRestrictedState φ eligible σ a=σ a:=by
      intro a ha
      simp [physicallyRestrictedState,hsupport c hw a ha]
    apply congrArg (fun z:ℝ=>(if root∈R c then w c else 0)*z)
    rw [patternValue_indicator,patternValue_indicator]
    congr 1
    apply propext
    constructor <;> intro hh a ha
    · rw [←hagree a (Finset.mem_sdiff.mp ha).1]
      exact hh a ha
    · rw [hagree a (Finset.mem_sdiff.mp ha).1]
      exact hh a ha
end Oberwolfach
