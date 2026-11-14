module

public import Oberwolfach.LongRawAdaptivePatternLoad
public import Oberwolfach.AdaptiveDeletedPairSumBound

@[expose] public section
/-! Combine the realised adaptive-deletion loss with endpoint incidence and
near/far pair-weight bounds. These deterministic hypotheses are to be
verified for the actual seed families and deleted physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U I:Type} [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]

theorem long_raw_adaptive_pattern_load_degree_bound
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (R:I→Finset (LongRawHubResource n U)) (w:I→ℝ) (hw:∀i,0≤w i)
    (F:Finset (Sym2 (Fin n))) (root:LongRawHubResource n U) (target:ℝ)
    (tail head:LongRawHubResource n U→Fin n) (D M N:ℝ) (hM:0≤M) (hN:0≤N)
    (Sroot Troot:Finset (Fin n)):
    let state:=longRawHubState P π d raw g j
    let T:=bernoulliVertexSet state
    let S:=longRawSurvivingResources P π d raw g j F
    let survived:=fun z=>decide (z∈S)
    let Deleted:=T.filter (fun z=>∃edge,typedResourcePhysical π
      ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge ∧ edge∈F)
    (∀x,(∑a,if a∈Deleted ∧ tail a=x then (1:ℝ) else 0)≤D)→
    (∀x,(∑a,if a∈Deleted ∧ head a=x then (1:ℝ) else 0)≤D)→
    (∀a∈Deleted,resourceOmittedPairWeight R w root a≤
      (if tail a∈Sroot ∨ head a∈Troot then M else N))→
    |resourcePatternLoad R w (fun _ _=>true) root survived-target|≤
      |resourcePatternLoad R w (fun _ _=>true) root state-target|+
        D*((Sroot.card+Troot.card:ℝ)*M+(n:ℝ)*N) :=by
  intro state T S survived Deleted hout hin hpair
  have hb:=adaptive_deleted_pair_sum_bound Deleted tail head D M N hM hN hout hin Sroot Troot
    (resourceOmittedPairWeight R w root) hpair
  have hp:=long_raw_adaptive_pattern_load_target_bound P π d raw g j R w hw F root target
  change |resourcePatternLoad R w (fun _ _=>true) root survived-target|≤
      |resourcePatternLoad R w (fun _ _=>true) root state-target|+
        ∑z∈Deleted,resourceOmittedPairWeight R w root z at hp
  exact hp.trans (add_le_add (le_refl _) (by simpa using hb))
end Oberwolfach
