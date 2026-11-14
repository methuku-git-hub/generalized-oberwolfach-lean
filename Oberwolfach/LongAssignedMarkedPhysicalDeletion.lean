module

public import Oberwolfach.LongMarkedPhysicalDeletionLoad
public import Oberwolfach.LongAssignedSeedFunctionBounds

@[expose] public section
/-! The original assigned marked seed weights retain their target-load
estimates under every later bounded physical-rim deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_assigned_marked_seed_load_after_physical_deletion
    (hn:0<n) (hu:Fintype.card U≤n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m d:ℕ) (hm:3≤m) (θ D:ℝ) (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (weight:(Fin (m+1)→Fin n)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤longAssignedMarkedSeed F hF K m d θ D π weight W ∧
      longAssignedMarkedSeed F hF K m d θ D π weight W≤B/(n:ℝ)^m)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (δ:ℝ)
    (hDel:∀x,(Del.degree x:ℝ)≤δ) (root:LongRawHubResource n U) (target:ℝ):
    let W:=longAssignedMarkedSeed F hF K m d θ D π weight
    let state:=longRawHubState P π d raw g j
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let survived:=fun z=>decide (z∈S)
    |resourcePatternLoad typedMarkedOccurrenceResources W (fun _ _=>true) root survived-target|≤
      |resourcePatternLoad typedMarkedOccurrenceResources W (fun _ _=>true) root state-target|+
        10*δ*((m:ℝ)+1)^4*B/(n:ℝ) :=by
  intro W state S survived
  exact long_marked_fixed_load_after_physical_deletion_uniform P Del π d raw g j hm hn hu W B hB hw root target δ hDel
end Oberwolfach
