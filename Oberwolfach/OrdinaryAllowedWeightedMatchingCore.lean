module

public import Oberwolfach.OrdinaryOriginalWeightedMatchingCore
public import Oberwolfach.PreparationWeightsFromAllowedThreshold

@[expose] public section
/-! The original regular host supplies both seed weights and the matching
core on the assigned sampling law, preserving an arbitrary prior event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryAllowedWeightedCoreFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_allowed_weighted_matching_core
    (Allowed:Set ℕ) (hAllowedSet:Allowed.Nonempty) (hValid:∀s∈Allowed,3≤s)
    (K d m k:ℕ) (hd:2≤d) (hm:3≤m) (hlen:m+1=(k+2)*2)
    (ρ₀ t ξ ζ smin α θ τ:ℝ)
    (hρ₀:0<ρ₀) (ht:0<t) (hξ:0<ξ) (hζ:0<ζ) (hsmin:0<smin)
    (hα:0<α) (hθ:0<θ) (hτ:0<τ)
    (hratio:successorCycleRatio k+α/2≤1/2+α):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv c:ℝ) (D:ℕ)
    (hslo:smin≤rsv) (hs1:rsv≤1/100) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρlo:ρ₀≤ initialIndexDensity U D) (hρ1:initialIndexDensity U D≤1) (hD:0<D)
    (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (π:Equiv.Perm (Fin n))
    (hdegree:(allowedThreshold Allowed+α)*(n:ℝ)≤D)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    ∃sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d,
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (m+1)→Fin n)→ℝ,
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ),
    let p:=initialIndexDensity U D*rsv/2
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m seed
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w;
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+ζ)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ z.1) :=by
  have hhalf:1/2≤allowedThreshold Allowed:=allowedThreshold_half_le hAllowedSet hValid
  have hbdd:BddAbove (cycleThreshold '' Allowed):=by
    refine ⟨1,?_⟩
    rintro x ⟨s,hs,rfl⟩
    exact cycleThreshold_le_one s
  have hthreshold:∀s∈Allowed,cycleThreshold s≤allowedThreshold Allowed:=by
    intro s hs
    exact le_csSup hbdd ⟨s,hs,rfl⟩
  obtain ⟨N,hmain⟩:=ordinary_original_weighted_matching_core K d m k hd hm hlen ρ₀ t ξ ζ smin
    (allowedThreshold Allowed) α θ τ hρ₀ ht hξ hζ hsmin hhalf hα hθ hτ hratio
  refine ⟨N,?_⟩
  intro n hn hn0 U _ _ hUn F hF hK i₀ rsv c D hslo hs1 hθ1 hc hda hρlo hρ1 hD
    hAllowed hsclass hclass P hreg π hdegree hnoshort
  exact hmain n hn hn0 U hUn F hF hK i₀ rsv c D hslo hs1 hθ1 hc hda hρlo hρ1 hD
    Allowed hAllowed hthreshold hsclass hclass P hreg π hdegree hnoshort
end Oberwolfach
