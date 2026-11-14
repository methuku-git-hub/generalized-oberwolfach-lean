module

public import Oberwolfach.ResidualActualReservedMatchingContinuation

@[expose] public section
/-! Interpret the forbidden-index set as the absorber target family. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem forbidden_index_avoids_absorber_target
    {V U:Type} [Fintype U] [DecidableEq U] (Abs:U→Finset V)
    (u:U) (v:V) (h:u∉(Finset.univ.filter (fun i=>v∈Abs i))):v∉Abs u:=by
  intro hv
  exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩)
end Oberwolfach
