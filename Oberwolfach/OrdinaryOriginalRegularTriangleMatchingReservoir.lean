module

public import Oberwolfach.OrdinaryAssignedRegularTriangleMatchingReservoir
public import Oberwolfach.OrdinaryRegularTriangleMatchingHostInputs
public import Oberwolfach.OrdinaryAssignedVortexMatchingReservoir
public import Oberwolfach.OrdinaryAssignedVortexSamplingData
public import Oberwolfach.OrdinaryMatchingAndProtectedReservoirHighProbability

@[expose] public section
/-! Instantiate the assigned matching and protected-reservoir theorem with
exactly the categorical recipe used by the vortex sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) originalRegularTriangleMatchingReservoirFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_original_regular_triangle_matching_reservoir
    (K d m:ℕ) (hd:2≤d) (hm:3≤m) (ρ₀ BM t ξ ζ:ℝ)
    (hρ₀:0<ρ₀) (hBM:0<BM) (ht:0<t) (hξ:0<ξ) (hζ:0<ζ)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (α smin ω:ℝ)
    (hα:0<α) (hsmin:0<smin) (hsmin1:smin≤1) (hω:0<ω):
    ∃εabs εtrans εsample:ℝ,0<εabs ∧ 0<εtrans ∧ 0<εsample ∧
    ∀mRes:ℕ,∃aRes bRes tR:ℕ,1≤tR ∧ ∀tRes fRes:ℕ,∃N:ℕ,
    ∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→ω*n≤(Fintype.card U:ℝ)→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ) (D:ℕ)
    (hslo:smin≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρlo:ρ₀≤ initialIndexDensity U D) (hρ1:initialIndexDensity U D≤1) (hD:0<D)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀),
    ∃sampling:OrdinaryAssignedVortexSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d,
    ∀(P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (π:Equiv.Perm (Fin n))
    (θhost:ℝ) (hθhost:1/2≤θhost) (hθcycle:cycleThreshold 3≤θhost)
    (hdegree:(θhost+α)*(n:ℝ)≤D)
    (τ A:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ A BM weight)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (hw0:∀i C,0≤w i C) (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ),
    let p:=initialIndexDensity U D*rsv/2
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let Aref:=fun σ:RawWheelOutcome (Fin n) U Bool Bool=>
      OrdinaryUniformProtectedReservoirEvent 3 mRes tRes fRes aRes bRes εabs
        (rawWheelGraph P σ\permutationConflictGraph π (3*d)) (permutationConflictGraph π (3*d)) (rawWheelSpokes π d σ false)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w;
    1-εE≤(μ.sigma ν).probability E→
    1-((εE+(1/(n:ℝ)+2/(n:ℝ)^2))+ζ)≤(μ.sigma ν).probability (fun z=>
      (E z ∧ Aref (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) ∧
      OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ z.1) :=by
  obtain ⟨εabs,εtrans,εsample,hεabs,hεtrans,hεsample,hmain⟩:=
    ordinary_assigned_regular_triangle_matching_reservoir K d m hd hm ρ₀ BM t ξ ζ
      hρ₀ hBM ht hξ hζ BO hBO α smin ω hα hsmin hsmin1 hω
  refine ⟨εabs,εtrans,εsample,hεabs,hεtrans,hεsample,?_⟩
  intro mRes
  obtain ⟨aRes,bRes,tR,htR,hmain⟩:=hmain mRes
  refine ⟨aRes,bRes,tR,htR,?_⟩
  intro tRes fRes
  obtain ⟨N,hmain⟩:=hmain tRes fRes
  refine ⟨N,?_⟩
  intro n hn hn0 U _ _ hUn hUlo F hF hK i₀ rsv θ c D hslo hs1 hθ hθ1 hc hda hρlo hρ1 hD
    Allowed hAllowed hsclass hclass
  obtain ⟨sampling⟩:=ordinary_assigned_vortex_sampling_data hn0 hD F hF Allowed hAllowed K hK i₀ rsv θ c ρ₀ smin d hd
    hρ₀ hρlo hρ1 hsmin hslo hs1 hθ hθ1 hc hda hsclass hclass
  refine ⟨sampling,?_⟩
  intro P hreg π θhost hθhost hθcycle hdegree τ A weight hw w hw0 hwupper hnoshort R _ ν E εE p q s p₂ Aref μ wM wO hE
  exact hmain n hn hn0 U hUn hUlo F hF hK i₀ rsv θ c D hslo hs1 hθ hθ1 hc hda hρlo hρ1 hD
    Allowed hAllowed hsclass hclass sampling P hreg π θhost hθhost hθcycle hdegree τ A weight hw w hw0 hwupper hnoshort ν E εE hE
end Oberwolfach
