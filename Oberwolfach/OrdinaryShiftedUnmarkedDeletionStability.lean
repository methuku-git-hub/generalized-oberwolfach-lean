module

public import Oberwolfach.OrdinaryShiftedUnmarkedLongLoad
public import Oberwolfach.LongOrdinaryPhysicalDeletionLoad

@[expose] public section
/-! The ordinary unmarked candidate loads inherit the physical-deletion
bound on the same sample, because their patterns never use shifted arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] {m b:ℕ}

theorem ordinary_shifted_unmarked_load_deletion_stability
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (hm:2≤m) (hn:0<n) (hu:Fintype.card U≤n)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(n:ℝ)^m)
    (root:LongRawHubResource n U) (target δ:ℝ) (hD:∀x,(D.degree x:ℝ)≤δ):
    let R:=fun W=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding
    let old:=typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let new:=typedMarkedResourceState (ordinaryShiftedPairRims P π d (rawMarkedDeleteRims raw D.edgeFinset))
      (rawMarkedPairSpokes π d (rawMarkedDeleteRims raw D.edgeFinset) g j);
    |resourcePatternLoad R w (fun _ _=>true) root new-target|≤
      |resourcePatternLoad R w (fun _ _=>true) root old-target|+
        10*δ*((m:ℝ)+1)^4*B/(n:ℝ) :=by
  intro R old new
  have hh:=long_ordinary_fixed_load_after_physical_deletion_uniform P D π d raw g j hm hn hu w B hB hw root target δ hD
  dsimp only at hh
  have hs:(fun z=>decide (z∈longRawSurvivingResources P π d raw g j D.edgeFinset))=
      longRawHubState P π d (rawMarkedDeleteRims raw D.edgeFinset) g j:=by
    funext z
    rw [long_raw_surviving_state_is_raw_rim_deletion]
    simp [mem_bernoulliVertexSet]
  rw [hs] at hh
  have h1:=ordinary_shifted_unmarked_load_eq_long P π d g j raw orderedOrdinaryResources w root
  have h2:=ordinary_shifted_unmarked_load_eq_long P π d g j (rawMarkedDeleteRims raw D.edgeFinset) orderedOrdinaryResources w root
  rw [←h1,←h2] at hh
  exact hh
end Oberwolfach
