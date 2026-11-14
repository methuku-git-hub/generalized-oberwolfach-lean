module

public import Oberwolfach.OrdinaryOriginalRegularMatchingSeedWeights
public import Oberwolfach.PreparationWeightsFromAllowedThreshold
public import Oberwolfach.CommonMarkedDensityBounds

@[expose] public section
/-! Original allowed-cycle assumptions supply the threshold and, beyond a
uniform cutoff, both kinds of weights used by the matching construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 100000) allowedSeedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_allowed_threshold_matching_seed_weights
    (Allowed:Set ℕ) (hAllowed:Allowed.Nonempty) (hValid:∀s∈Allowed,3≤s)
    (K:ℕ) (α θ τ:ℝ) (hα:0<α) (hθ:0<θ) (hτ:0<τ):
    ∃k₀:ℕ,∀k:ℕ,k₀≤k→
    ∃BO:Fin K→ℝ,∃BM A:ℝ,(∀i,0<BO i) ∧ 0<BM ∧ 0<A ∧ ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hK:0<K) (hLengths:∀u,AllowedCycleLengths (F u) Allowed)
      (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (D:ℕ),
    P.IsRegularOfDegree D→(allowedThreshold Allowed+α)*n≤D→
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (((k+2)*2-1)+1)→Fin n)→ℝ,
      (∀i C,0≤w i C ∧ w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ A BM seed :=by
  have hhalf:1/2≤allowedThreshold Allowed:=allowedThreshold_half_le hAllowed hValid
  have hbdd:BddAbove (cycleThreshold '' Allowed):=by
    refine ⟨1,?_⟩
    rintro x ⟨s,hs,rfl⟩
    exact cycleThreshold_le_one s
  have hthreshold:∀s∈Allowed,cycleThreshold s≤allowedThreshold Allowed:=by
    intro s hs
    exact le_csSup hbdd ⟨s,hs,rfl⟩
  obtain ⟨k₀,hk₀⟩:=successorCycleRatio_eventually_margin α hα
  refine ⟨k₀,?_⟩
  intro k hk
  obtain ⟨BO,BM,A,hBO,hBM,hA,hweights⟩:=ordinary_original_regular_matching_seed_weights K k
    (allowedThreshold Allowed) α θ τ hα hθ hτ hhalf (hk₀ k hk)
  refine ⟨BO,BM,A,hBO,hBM,hA,?_⟩
  intro d
  obtain ⟨N,hN⟩:=hweights d
  refine ⟨N,?_⟩
  intro n hn hn0 U _ F hF hK hLengths P π D hreg hdeg
  exact hN n hn hn0 U F hF hK Allowed hLengths hthreshold P π D hreg hdeg
end Oberwolfach
