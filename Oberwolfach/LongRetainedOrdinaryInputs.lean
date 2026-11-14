module

public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! The ordinary-root load inputs for discarded indices are automatic;
only retained indices require a fractional-cycle-weight argument. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] {C:Fin K→Type} [∀i,Fintype (C i)]

theorem long_ordinary_active_inputs_from_retained
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (θ D p t τ:ℝ) (ht:0≤t)
    (hub:∀i,C i→U) (base:∀i,C i→ℝ)
    (R:∀i,C i→Finset ((Fin n×Fin n)⊕(Fin n×U)))
    (state:((Fin n×Fin n)⊕(Fin n×U))→Bool):
    let w:=fun i c=>(longAssignedKeptOrdinaryContribution F hF K θ i (hub i c)/
      longAssignedApproxOrdinaryWeight F hF K m θ (hub i c))*base i c
    (∀i∈longRetainedSeedIndices F hF K θ,∀root,state root=true→
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) root state-
        ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root|≤
        t+τ*ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root)→
    ∀i root,state root=true→
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) root state-
        ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root|≤
        t+τ*ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
          (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
            longAssignedApproxOrdinaryWeight F hF K m θ u) root :=by
  intro w hret i root hactive
  by_cases hi:i∈longRetainedSeedIndices F hF K θ
  · exact hret i hi root hactive
  · have hzero:=long_nonretained_seed_exact_target F hF K m θ D p i hi (hub i) (base i) (R i) state root
    have hnot:¬∃u,θ/(100*(K:ℝ))≤ordinaryAssignedFraction F hF K u (some i):=by
      simpa only [longRetainedSeedIndices,Finset.mem_filter,Finset.mem_univ,true_and] using hi
    have hf:∀u,longAssignedKeptFraction F hF K θ i u=0:=
      fun u=>(long_unretained_kept_fraction_zero F hF K θ i hnot u).1
    have hc:∀u,longAssignedKeptOrdinaryContribution F hF K θ i u=0:=
      fun u=>(long_unretained_kept_fraction_zero F hF K θ i hnot u).2
    have htarget:ordinarySeedRootTarget D p θ (longAssignedKeptFraction F hF K θ i)
      (fun u=>longAssignedKeptOrdinaryContribution F hF K θ i u/
        longAssignedApproxOrdinaryWeight F hF K m θ u) root=0:=by
      cases root <;> simp [ordinarySeedRootTarget,hf,hc]
    rw [hzero,htarget]
    simpa using ht
end Oberwolfach
