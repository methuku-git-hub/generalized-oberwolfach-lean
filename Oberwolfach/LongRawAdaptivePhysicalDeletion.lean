module

public import Oberwolfach.LongRawAdaptivePatternDegreeBound
public import Oberwolfach.LongRawDeletedIncidence

@[expose] public section
/-! The actual physical deletion graph supplies both auxiliary incidence
bounds; only the seed-specific near/far pair estimates remain to be shown. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U I:Type} [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]

theorem long_raw_adaptive_pattern_load_physical_deletion
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (R:I→Finset (LongRawHubResource n U)) (w:I→ℝ) (hw:∀i,0≤w i)
    (root:LongRawHubResource n U) (target δ M N:ℝ) (hM:0≤M) (hN:0≤N)
    (hD:∀x,(D.degree x:ℝ)≤δ) (Sroot Troot:Finset (Fin n)):
    let state:=longRawHubState P π d raw g j
    let T:=bernoulliVertexSet state
    let S:=longRawSurvivingResources P π d raw g j D.edgeFinset
    let survived:=fun z=>decide (z∈S)
    let Deleted:=T.filter (fun z=>∃edge,typedResourcePhysical π
      ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge ∧ edge∈D.edgeFinset)
    (∀a∈Deleted,resourceOmittedPairWeight R w root a≤
      (if longRawResourceTail a∈Sroot ∨ longRawResourceHead a∈Troot then M else N))→
    |resourcePatternLoad R w (fun _ _=>true) root survived-target|≤
      |resourcePatternLoad R w (fun _ _=>true) root state-target|+
        2*δ*((Sroot.card+Troot.card:ℝ)*M+(n:ℝ)*N) :=by
  intro state T S survived Deleted hpair
  have hi:=long_raw_deleted_resource_incidence_bound P D π d raw g j δ hD
  exact long_raw_adaptive_pattern_load_degree_bound P π d raw g j R w hw D.edgeFinset root target
    longRawResourceTail longRawResourceHead (2*δ) M N hM hN Sroot Troot hi.1 hi.2 hpair
end Oberwolfach
