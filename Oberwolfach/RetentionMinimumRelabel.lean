module

public import Oberwolfach.UniformStartRetentionMinimum

@[expose] public section
/-! Reindexing all starts and preserving their eligible-hub counts does not
change the common retention size. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Nonempty V] [Nonempty W] [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq Z]
theorem start_retention_minimum_relabel
    (f:W≃V) (A:V→Finset U) (A':W→Finset Z)
    (hcard:∀ w,(A' w).card=(A (f w)).card):
    startRetentionMinimum A'=startRetentionMinimum A := by
  apply le_antisymm
  · obtain ⟨v,hv⟩:=startRetentionMinimum_eq_some A
    have hh:=startRetentionMinimum_le A' (f.symm v)
    rw [hcard,Equiv.apply_symm_apply,←hv] at hh
    exact hh
  · obtain ⟨w,hw⟩:=startRetentionMinimum_eq_some A'
    have hh:=startRetentionMinimum_le A (f w)
    rw [←hcard,←hw] at hh
    exact hh
end Oberwolfach
