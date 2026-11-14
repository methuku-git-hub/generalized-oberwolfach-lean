module

public import Oberwolfach.CandidateOrdinaryAssignedVortexExactSamplingData
public import Oberwolfach.CandidateOrdinaryAssignedSamplingParameters
public import Oberwolfach.CandidateOrdinaryAssignedNamedSamplingWitness

@[expose] public section
/-! The original assigned recipe leaves a positive density of physical edges
outside the reference and approximate-matching colours. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_unused_physical_probability_lower_candidate
    {n D:ℕ} (hn:0<n) (hD:0<D)
    {U:Type} [Fintype U] [DecidableEq U] (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ₀ smin:ℝ) (d:ℕ) (hd:2≤d)
    (hρ₀:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hsmin:0<smin) (hslo:smin≤rsv) (hs1:rsv≤1/100)
    (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c) (hda:1/θ≤d)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,i₀∈factorShortCandidates (F w) K)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d):
    ρ₀*θ/2≤sampling.u :=by
  let ρ:=initialIndexDensity U D
  have hρ:0<ρ:=hρ₀.trans_le hρlo
  have hDreal:0<(D:ℝ):=by exact_mod_cast hD
  have hsize:ρ*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    dsimp [ρ,initialIndexDensity]
    field_simp
  have hs0:0≤rsv:=(hsmin.trans_le hslo).le
  have hh:=ordinary_class_assigned_sampling_parameters_candidate hn F hF K hK i₀ rsv θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρhi hDreal hsize Allowed hAllowed hsclass hclass
  have hpoint:∀w,θ/2≤1-rsv-ordinaryAssignedLongWeight F hF K θ c w-
      ordinaryAssignedShortWeight F hF K i₀ rsv θ c w:=by
    intro w
    have hw:=(hh.1 w).2.2.2.1
    simpa only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hw
  obtain ⟨u,hu,hp₂,hp₂lo,hEq,hUD,hrecipe⟩:=
    ordinary_assigned_named_sampling_witness_candidate hn F hF Allowed hAllowed K hK i₀ rsv θ c ρ D d hd
      hs0 hs1 hθ hθ1 hc hda hρ hρhi hDreal hsize hsclass hclass
  have huEq:u=sampling.u:=by
    have hs:=sampling.hphysical
    dsimp [ρ] at hEq
    linarith
  have hsum:((Fintype.card U:ℝ)*(θ/2))≤
      ∑w:U,(1-rsv-ordinaryAssignedLongWeight F hF K θ c w-
        ordinaryAssignedShortWeight F hF K i₀ rsv θ c w):=by
    have hs:=Finset.sum_le_sum (fun w (_:w∈(Finset.univ:Finset U))=>hpoint w)
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hs
  rw [huEq] at hUD
  have hDmul:ρ*θ/2*(D:ℝ)≤sampling.u*(D:ℝ):=by nlinarith [hUD,hsize,hsum]
  have hρbound:ρ₀*θ/2≤ρ*θ/2:=by nlinarith
  exact hρbound.trans ((mul_le_mul_iff_right₀ hDreal).mp (by simpa only [mul_comm] using hDmul))
end Oberwolfach
