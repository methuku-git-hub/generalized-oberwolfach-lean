module

public import Oberwolfach.LongRawAdaptiveOmittedLoad
public import Oberwolfach.BernoulliVertexSampling

@[expose] public section
/-! Express the deterministic deletion estimate in the same fixed-pattern
loads used by the actual long-family concentration event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U I:Type} [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]

theorem long_raw_adaptive_pattern_load_after_rim_deletion
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (R:I→Finset (LongRawHubResource n U)) (w:I→ℝ) (hw:∀i,0≤w i):
    ∀(F:Finset (Sym2 (Fin n))) (root:LongRawHubResource n U),
    let state:=longRawHubState P π d raw g j
    let T:=bernoulliVertexSet state
    let S:=longRawSurvivingResources P π d raw g j F
    let survived:=fun z=>decide (z∈S)
    let Deleted:=T.filter (fun z=>∃edge,typedResourcePhysical π
      ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge ∧ edge∈F)
    |resourcePatternLoad R w (fun _ _=>true) root survived-
      resourcePatternLoad R w (fun _ _=>true) root state|≤
      ∑z∈Deleted,resourceOmittedPairWeight R w root z :=by
  intro F root state T S survived Deleted
  have hs:bernoulliVertexSet survived=S:=by
    ext z
    simp [mem_bernoulliVertexSet,survived]
  have h:=long_raw_adaptive_omitted_load_after_rim_deletion P π d raw g j R w hw F root
  change |resourceRootOmittedLoad R w (·∈S) root-resourceRootOmittedLoad R w (·∈T) root|≤
      ∑z∈Deleted,resourceOmittedPairWeight R w root z at h
  change |resourceRootOmittedLoad R w (·∈S) root-resourceRootOmittedLoad R w (fun z=>z∈bernoulliVertexSet state) root|≤
      ∑z∈Deleted,resourceOmittedPairWeight R w root z at h
  rw [bernoulli_root_load_pattern R w root state] at h
  rw [←hs,bernoulli_root_load_pattern R w root survived] at h
  exact h
theorem long_raw_adaptive_pattern_load_target_bound
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (R:I→Finset (LongRawHubResource n U)) (w:I→ℝ) (hw:∀i,0≤w i)
    (F:Finset (Sym2 (Fin n))) (root:LongRawHubResource n U) (target:ℝ):
    let state:=longRawHubState P π d raw g j
    let T:=bernoulliVertexSet state
    let S:=longRawSurvivingResources P π d raw g j F
    let survived:=fun z=>decide (z∈S)
    let Deleted:=T.filter (fun z=>∃edge,typedResourcePhysical π
      ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge ∧ edge∈F)
    |resourcePatternLoad R w (fun _ _=>true) root survived-target|≤
      |resourcePatternLoad R w (fun _ _=>true) root state-target|+
        ∑z∈Deleted,resourceOmittedPairWeight R w root z :=by
  intro state T S survived Deleted
  have h:=long_raw_adaptive_pattern_load_after_rim_deletion P π d raw g j R w hw F root
  change |resourcePatternLoad R w (fun _ _=>true) root survived-
      resourcePatternLoad R w (fun _ _=>true) root state|≤
      ∑z∈Deleted,resourceOmittedPairWeight R w root z at h
  have ht:=abs_sub_le (resourcePatternLoad R w (fun _ _=>true) root survived)
    (resourcePatternLoad R w (fun _ _=>true) root state) target
  linarith
end Oberwolfach
