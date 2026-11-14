module

public import Oberwolfach.LongAssignedMixedTargetProfile
public import Oberwolfach.MarkedActiveSeedTargets
public import Oberwolfach.OrdinaryRetainedActiveSeedBounds
public import Oberwolfach.OrderedOrdinaryLocality

@[expose] public section
/-! The marked and ordinary concentration targets are precisely the
fixed long-class coefficient profiles, including zeroed rare lengths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def longAssignedKeptFraction (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (K:ℕ) (θ:ℝ) (i:Fin K) (u:U):ℝ:=
  if θ/(100*(K:ℝ))≤ordinaryAssignedFraction F hF K u (some i)
    then ordinaryAssignedFraction F hF K u (some i) else 0

theorem long_assigned_kept_fraction_contribution
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K:ℕ) (θ:ℝ) (i:Fin K) (u:U):
    longAssignedKeptOrdinaryContribution F hF K θ i u=
      (1-θ)*longAssignedKeptFraction F hF K θ i u:=by
  unfold longAssignedKeptOrdinaryContribution longAssignedKeptFraction
  split_ifs <;> ring

theorem long_assigned_marked_seed_target
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ D p k:ℝ)
    (root:((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)):
    markedSeedRootTarget m p k (longAssignedIntervalProbability F hF K m θ)
      (longAssignedSpokeProbability F hF K m θ) true true root=
    longAssignedMixedTarget F hF K m θ D p k none root := by
  cases root with
  | inl e => cases e <;> rfl
  | inr a => rcases a with ⟨b,v,u⟩;cases b <;>
      simp [markedSeedRootTarget,longAssignedMixedTarget,longAssignedIntervalProbability,longAssignedSpokeProbability]

theorem long_assigned_ordinary_seed_target
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ D p k:ℝ) (i:Fin K) (root:(Fin n×Fin n)⊕(Fin n×U)):
    ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
      (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
        longAssignedApproxOrdinaryWeight F hF K m θ u) root=
    longAssignedMixedTarget F hF K m θ D p k (some i) (orderedOrdinaryResourceEmbedding root) := by
  cases root with
  | inl xy=>
    simp only [ordinarySeedRootTarget,orderedOrdinaryResourceEmbedding,longAssignedMixedTarget]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    exact (long_assigned_kept_fraction_contribution F hF K θ i u).symm
  | inr vu=>rcases vu with ⟨v,u⟩;rfl
end Oberwolfach
