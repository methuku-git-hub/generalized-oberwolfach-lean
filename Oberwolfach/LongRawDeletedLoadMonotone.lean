module

public import Oberwolfach.LongRawDeletedStateBool
public import Oberwolfach.ResourceRootOmittedMonotonicity
public import Oberwolfach.BernoulliVertexSampling

@[expose] public section
/-! The fixed nonnegative root-omitted load can only decrease under a
physical rim deletion, including at roots that are themselves deleted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U I:Type} [Fintype U] [DecidableEq U] [Fintype I]

theorem long_raw_pattern_load_nonincreasing_after_rim_deletion
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n)))
    (R:I→Finset (LongRawHubResource n U)) (w:I→ℝ) (hw:∀i,0≤w i)
    (root:LongRawHubResource n U):
    resourcePatternLoad R w (fun _ _=>true) root
        (longRawHubState P π d (rawMarkedDeleteRims raw F) g j) ≤
      resourcePatternLoad R w (fun _ _=>true) root (longRawHubState P π d raw g j) :=by
  let old:=longRawHubState P π d raw g j
  let new:=longRawHubState P π d (rawMarkedDeleteRims raw F) g j
  have hsub:∀a,a∈bernoulliVertexSet new→a∈bernoulliVertexSet old:=by
    intro a ha
    rw [←long_raw_surviving_state_is_raw_rim_deletion P π d raw g j F] at ha
    exact (long_raw_surviving_resources_subset P π d raw g j F) ha
  have hh:=resourceRootOmittedLoad_mono R w hw (fun a=>a∈bernoulliVertexSet old)
    (fun a=>a∈bernoulliVertexSet new) hsub root
  rw [bernoulli_root_load_pattern,bernoulli_root_load_pattern] at hh
  exact hh
end Oberwolfach
