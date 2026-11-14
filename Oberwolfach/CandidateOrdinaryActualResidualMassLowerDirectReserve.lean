module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryActualResidualMassLower
public import Oberwolfach.OrdinaryActualResidualMassLower
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedRetainedMassDirectReserve
public import Oberwolfach.RetainedRawHubStartLower
public import Oberwolfach.OrdinaryAssignedRetainedMass
public import Oberwolfach.ResidualLongMassArithmetic
public import Oberwolfach.ActualResidualSumIndices

@[expose] public section
/-! Derive the actual full-selection mass from the original start counts,
retention row bound, and the selected ordinary-cycle mass. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance ordinaryActualResidualMassFin_candidate_direct_reserve (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_actual_residual_full_mass_lower_candidate_direct_reserve
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100)
    (m d:ℕ) (hm:7≤m) (hd:1≤d) (θ:ℝ) (hθ:0<θ) (hθ1:θ≤1/100)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (ζ errOrd err:ℝ)
    (hgood:RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (w:U)
    (hcounts:∀g:Bool,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/d|<(n:ℝ)^(3/4:ℝ)/d):
    let A:=retainedMarkedIndex π d σ false t Jret w
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) x true}
    ∀{J:Type} [DecidableEq J] {S:Set (Fin n)} (a:ActualResidualData (K:=A⊕B) (J:=J) ((F w).induce S))
    (hc:a.c=m+1) (hd':a.d=d) (hs₁:a.s₁=firstSumIndices) (hs₂:a.s₂=secondSumIndices)
    (hC:(n:ℝ)*((1-θ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i))-errOrd≤
      ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ))
    (herror:(n:ℝ)*(∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g)/d+
       (((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+errOrd≤err*n),
    (1-rsv-2*θ-err)*n≤
      ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ)+
        ((a.c*a.d-1:ℕ):ℝ)*(a.s₁.card+a.s₂.card):=by
  intro A B J _ S a hc hd' hs₁ hs₂ hC herror
  have hA:a.s₁.card=Fintype.card A:=by
    rw [hs₁]
    simpa only [Fintype.card_coe] using (Fintype.card_congr (firstSumIndexEquiv (A:=A) (B:=B))).symm
  have hB:a.s₂.card=Fintype.card B:=by
    rw [hs₂]
    simpa only [Fintype.card_coe] using (Fintype.card_congr (secondSumIndexEquiv (A:=A) (B:=B))).symm
  have hstart:=retained_raw_hub_start_count_lower π d hd σ false true t Jret ζ
    (ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w false) (ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w true)
    ((n:ℝ)^(3/4:ℝ)/d) hgood w (by simpa using hcounts false) (by simpa using hcounts true)
  have hS:(n:ℝ)*(∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g)/d-
      (2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)≤(a.s₁.card+a.s₂.card:ℕ):=by
    simp only [Fintype.card_fin,retainedAndRawIntervalIndex,Fintype.card_sum,Nat.cast_add] at hstart
    simp only [Fintype.sum_bool,hA,hB,Nat.cast_add]
    dsimp [A,B] at *
    convert hstart using 1 <;> ring
  have hprob0:=ordinary_assigned_retained_mass_candidate_direct_reserve hn F hF Allowed hAllowed K hK i₀ rsv θ ((m:ℝ)+1)
    hrs0 hrs1 hθ hθ1 (by
      have hm8 : 8 ≤ m+1 := by omega
      exact_mod_cast hm8) hClassReserve w
  have hprob:1-(rsv+2*θ)≤((m:ℝ)+1)*
      (∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g)+
      (1-θ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i):=by
    simp only [Fintype.sum_bool,ordinaryAssignedMarkedProbability,Bool.false_eq_true,ite_false,ite_true,zero_add]
    linarith
  have hcpos:(1:ℝ)≤((m:ℝ)+1)*(d:ℝ):=by
    have hmR:(1:ℝ)≤m:=by
      have hm1:1≤m:=by omega
      exact_mod_cast hm1
    have hdR:(1:ℝ)≤d:=by exact_mod_cast hd
    nlinarith
  have hcoef:(((m+1)*d-1:ℕ):ℝ)=((m:ℝ)+1)*(d:ℝ)-1:=by
    rw [Nat.cast_sub (by nlinarith : 1≤(m+1)*d)]
    push_cast
    ring
  have hresult:=residual_full_mass_from_sampled_counts n ((m:ℝ)+1) d
    (∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g)
    (∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i) θ (rsv+2*θ)
    (2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n) errOrd err (by positivity) (by exact_mod_cast hd) hcpos
    ((a.s₁.card+a.s₂.card:ℕ):ℝ) ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ)
    hS hC hprob (by simpa [hcoef] using herror)
  simp only [hc,hd',hcoef,Nat.cast_add] at hresult ⊢
  convert hresult using 1 <;> ring
end Oberwolfach
