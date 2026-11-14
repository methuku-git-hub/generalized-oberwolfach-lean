module

public import Oberwolfach.OrdinaryAssignedVortexSamplingWitness

@[expose] public section
/-! Categorical-law witnesses for the named original ordinary sampling
recipe, with the vortex mean and both positive marginal lower bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

structure OrdinaryAssignedVortexSamplingData {n D:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ) where
  u:ℝ
  hp:0≤ initialIndexDensity U D*rsv/2
  hp₂:0≤ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
  hu:0≤u
  hsum:2*(initialIndexDensity U D*rsv/2)+2*0+
    2*ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D+2*0+u≤1
  hpmin:ρ₀*smin≤2*(initialIndexDensity U D*rsv/2)
  hsmin:ρ₀*smin≤rsv
  hrsv:rsv≤1
  hq:∀w j,0≤ordinaryAssignedMarkedProbability F hF K θ c w j
  hQ:∀w,∑j,ordinaryAssignedMarkedProbability F hF K θ c w j≤1/8
  hs:∀w j,0≤ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w j
  hS:∀w,∑j,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w j≤
    intervalUncoveredProbability d (∑j,ordinaryAssignedMarkedProbability F hF K θ c w j)
  hfalse:∀w,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w false=rsv

theorem ordinary_assigned_vortex_sampling_data {n D:ℕ} (hn:0<n) (hD:0<D)
    {U:Type} [Fintype U] [DecidableEq U] (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ) (hd:2≤d)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hsmin:0<smin) (hslo:smin≤rsv) (hs1:rsv≤1/100)
    (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c) (hda:1/θ≤d)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,factorPreparationClass (F w) K=some i₀):
    Nonempty (OrdinaryAssignedVortexSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d) :=by
  obtain ⟨u,hp,hp₂,hu,hsum,hpmin,hsmin',hrsv,hpeq,hq,hQ,hs,hS,hfalse⟩:=
    ordinary_assigned_vortex_sampling_witness hn hD F hF Allowed hAllowed K hK i₀ rsv θ c ρ₀ smin d hd
      hρ₀ hρlo hρhi hsmin hslo hs1 hθ hθ1 hc hda hsclass hclass
  exact ⟨⟨u,hp,hp₂,hu,hsum,hpmin,hsmin',hrsv,hq,hQ,hs,hS,hfalse⟩⟩
end Oberwolfach
