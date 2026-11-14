module

public import Oberwolfach.RetainedRawHubStartLower
public import Oberwolfach.LongAssignedTotalSamplingMass
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
local instance longActualResidualMassFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_actual_residual_full_mass_lower
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m d:ℕ) (hm:0<m) (hd:1≤d) (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (ζ errOrd err:ℝ)
    (hgood:RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (w:U)
    (hcounts:∀g:Bool,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/d|<(n:ℝ)^(3/4:ℝ)/d):
    let A:=retainedMarkedIndex π d σ false t Jret w
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) x true}
    ∀{J:Type} [DecidableEq J] (a:ActualResidualData (K:=A⊕B) (J:=J) (F w))
    (hc:a.c=m+1) (hd':a.d=d) (hs₁:a.s₁=firstSumIndices) (hs₂:a.s₂=secondSumIndices)
    (hC:(n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w))-errOrd≤
      ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ))
    (herror:(n:ℝ)*(∑g:Bool,longAssignedIntervalProbability F hF K m θ w g)/d+
       (((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+errOrd≤err*n),
    (1-(101/100:ℝ)*θ-err)*n≤
      ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ)+
        ((a.c*a.d-1:ℕ):ℝ)*(a.s₁.card+a.s₂.card):=by
  intro A B J _ a hc hd' hs₁ hs₂ hC herror
  have hA:a.s₁.card=Fintype.card A:=by
    rw [hs₁]
    simpa only [Fintype.card_coe] using (Fintype.card_congr (firstSumIndexEquiv (A:=A) (B:=B))).symm
  have hB:a.s₂.card=Fintype.card B:=by
    rw [hs₂]
    simpa only [Fintype.card_coe] using (Fintype.card_congr (secondSumIndexEquiv (A:=A) (B:=B))).symm
  have hstart:=retained_raw_hub_start_count_lower π d hd σ false true t Jret ζ
    (longAssignedIntervalProbability F hF K m θ w false) (longAssignedIntervalProbability F hF K m θ w true)
    ((n:ℝ)^(3/4:ℝ)/d) hgood w (by simpa using hcounts false) (by simpa using hcounts true)
  have hS:(n:ℝ)*(∑g:Bool,longAssignedIntervalProbability F hF K m θ w g)/d-
      (2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)≤(a.s₁.card+a.s₂.card:ℕ):=by
    simp only [Fintype.card_fin,retainedAndRawIntervalIndex,Fintype.card_sum,Nat.cast_add] at hstart
    simp only [Fintype.sum_bool,hA,hB,Nat.cast_add]
    dsimp [A,B] at *
    convert hstart using 1 <;> ring
  have hprob:=long_assigned_sampling_mass_lower hn hK m hm F hF θ hθ hθ1 w
  have hcpos:(1:ℝ)≤((m:ℝ)+1)*(d:ℝ):=by
    have hmR:(1:ℝ)≤m:=by exact_mod_cast hm
    have hdR:(1:ℝ)≤d:=by exact_mod_cast hd
    nlinarith
  have hcoef:(((m+1)*d-1:ℕ):ℝ)=((m:ℝ)+1)*(d:ℝ)-1:=by
    rw [Nat.cast_sub (by nlinarith : 1≤(m+1)*d)]
    push_cast
    ring
  have hresult:=residual_full_mass_from_sampled_counts n ((m:ℝ)+1) d
    (∑g:Bool,longAssignedIntervalProbability F hF K m θ w g)
    (∑i:Fin K,longAssignedKeptFraction F hF K θ i w) θ ((101/100:ℝ)*θ)
    (2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n) errOrd err (by positivity) (by exact_mod_cast hd) hcpos
    ((a.s₁.card+a.s₂.card:ℕ):ℝ) ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ)
    hS hC hprob (by simpa [hcoef] using herror)
  simpa only [hc,hd',hcoef,Nat.cast_add] using hresult
end Oberwolfach
