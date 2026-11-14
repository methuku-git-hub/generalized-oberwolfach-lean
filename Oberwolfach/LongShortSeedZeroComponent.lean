module

public import Oberwolfach.LongAssignedPositiveSeedLengths
public import Oberwolfach.LongAssignedMixedTargetProfile
public import Oberwolfach.ResourcePatternConcentration

@[expose] public section
/-! Artificial length-one and length-two indices contribute neither weight
nor target. No fractional cycle decomposition at those lengths is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U C:Type} [Fintype U] [Fintype C]

theorem long_short_ordinary_component_target_zero
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ D p k:ℝ) (i:Fin K) (hi:i.val+1<3)
    (root:((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)):
    longAssignedMixedTarget F hF K m θ D p k (some i) root=0 :=by
  have hz:∀u,longAssignedKeptOrdinaryContribution F hF K θ i u=0:=
    fun u=>(long_assigned_kept_below_three_zero F hF K i hi θ u).2
  cases root with
  | inl e=>cases e <;> simp [longAssignedMixedTarget,hz]
  | inr a=>rcases a with ⟨b,v,u⟩;cases b <;> simp [longAssignedMixedTarget,hz]

theorem long_short_ordinary_component_zero_load
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ D p k:ℝ) (i:Fin K) (hi:i.val+1<3)
    (hub:C→U) (base:C→ℝ)
    (R:C→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (root:((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)):
    resourcePatternLoad R (fun c=>(longAssignedKeptOrdinaryContribution F hF K θ i (hub c)/
      longAssignedApproxOrdinaryWeight F hF K m θ (hub c))*base c)
      (fun _ _=>true) root state = longAssignedMixedTarget F hF K m θ D p k (some i) root :=by
  have hz:∀u,longAssignedKeptOrdinaryContribution F hF K θ i u=0:=
    fun u=>(long_assigned_kept_below_three_zero F hF K i hi θ u).2
  rw [long_short_ordinary_component_target_zero F hF K m θ D p k i hi root]
  simp [resourcePatternLoad,hz]
/-- The ordinary-root hypotheses for these indices are automatic, with no
balanced cycle weights or minimum-degree condition for a padded length. -/
theorem long_short_ordinary_seed_exact_target
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ D p k:ℝ) (i:Fin K) (hi:i.val+1<3)
    (hub:C→U) (base:C→ℝ) (R:C→Finset ((Fin n×Fin n)⊕(Fin n×U)))
    (state:((Fin n×Fin n)⊕(Fin n×U))→Bool) (root:(Fin n×Fin n)⊕(Fin n×U)):
    resourcePatternLoad R (fun c=>(longAssignedKeptOrdinaryContribution F hF K θ i (hub c)/
      longAssignedApproxOrdinaryWeight F hF K m θ (hub c))*base c)
      (fun _ _=>true) root state = ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
        (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
          longAssignedApproxOrdinaryWeight F hF K m θ u) root :=by
  have hf:∀u,longAssignedKeptFraction F hF K θ i u=0:=
    fun u=>(long_assigned_kept_below_three_zero F hF K i hi θ u).1
  have hc:∀u,longAssignedKeptOrdinaryContribution F hF K θ i u=0:=
    fun u=>(long_assigned_kept_below_three_zero F hF K i hi θ u).2
  cases root with
  | inl xy=>simp [resourcePatternLoad,ordinarySeedRootTarget,hf,hc]
  | inr vu=>simp [resourcePatternLoad,ordinarySeedRootTarget,hf,hc]
/-- Every index discarded at every hub has zero contribution and hence
requires no parent fractional decomposition, regardless of its padded length. -/
theorem long_unretained_kept_fraction_zero
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K:ℕ) (θ:ℝ) (i:Fin K)
    (hnot:¬∃u,θ/(100*(K:ℝ))≤ordinaryAssignedFraction F hF K u (some i)):
    ∀u,longAssignedKeptFraction F hF K θ i u=0 ∧
      longAssignedKeptOrdinaryContribution F hF K θ i u=0 :=by
  intro u
  have h:¬θ/(100*(K:ℝ))≤ordinaryAssignedFraction F hF K u (some i):=by
    intro hc
    exact hnot ⟨u,hc⟩
  constructor
  · simp [longAssignedKeptFraction,h]
  · rw [long_assigned_kept_fraction_contribution]
    simp [longAssignedKeptFraction,h]

theorem long_unretained_ordinary_seed_exact_target
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ D p:ℝ) (i:Fin K)
    (hnot:¬∃u,θ/(100*(K:ℝ))≤ordinaryAssignedFraction F hF K u (some i))
    (hub:C→U) (base:C→ℝ) (R:C→Finset ((Fin n×Fin n)⊕(Fin n×U)))
    (state:((Fin n×Fin n)⊕(Fin n×U))→Bool) (root:(Fin n×Fin n)⊕(Fin n×U)):
    resourcePatternLoad R (fun c=>(longAssignedKeptOrdinaryContribution F hF K θ i (hub c)/
      longAssignedApproxOrdinaryWeight F hF K m θ (hub c))*base c)
      (fun _ _=>true) root state = ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
        (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
          longAssignedApproxOrdinaryWeight F hF K m θ u) root :=by
  have hf:∀u,longAssignedKeptFraction F hF K θ i u=0:=
    fun u=>(long_unretained_kept_fraction_zero F hF K θ i hnot u).1
  have hc:∀u,longAssignedKeptOrdinaryContribution F hF K θ i u=0:=
    fun u=>(long_unretained_kept_fraction_zero F hF K θ i hnot u).2
  cases root with
  | inl xy=>simp [resourcePatternLoad,ordinarySeedRootTarget,hf,hc]
  | inr vu=>simp [resourcePatternLoad,ordinarySeedRootTarget,hf,hc]
end Oberwolfach
