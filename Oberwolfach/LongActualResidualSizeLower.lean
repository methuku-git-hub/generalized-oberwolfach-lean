module

public import Oberwolfach.ActualResidualSizeLower
public import Oberwolfach.RetainedRawIntervalRootUpperGeneral
public import Oberwolfach.LongAssignedTotalSamplingUpper

@[expose] public section
/-! The residual retains the θ fraction, up to the sampled start and cycle
mass errors. This supplies the lower bound needed for matching capacity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_actual_residual_size_lower_from_counts
    {n K:ℕ} {U J:Type} [Fintype U] [DecidableEq U] [DecidableEq J]
    (hn:0<n) (m d:ℕ) (hm:0<m) (hd:0<d)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r) (w:U)
    (data:ActualResidualData (K:=retainedAndRawIntervalIndex π d σ false true r Jret w) (J:=J) (F w))
    (hc:data.c=m+1) (hd':data.d=d)
    (hs1:data.s₁=firstSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (hs2:data.s₂=secondSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (θ t err:ℝ) (hθ:θ≤1)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<t/(d:ℝ))
    (hC:((data.t.biUnion (fun j=>(data.C j).support.toFinset)).card:ℝ)≤
      (n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w))+err):
    θ*n-err-2*((m:ℝ)+1)*t≤(data.remaining.card:ℝ):=by
  have h1:data.s₁.card=Fintype.card (retainedMarkedIndex π d σ false r Jret w):=by
    rw [hs1]
    simpa only [Fintype.card_coe] using (Fintype.card_congr
      (firstSumIndexEquiv (A:=retainedMarkedIndex π d σ false r Jret w)
        (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))).symm
  have h2:data.s₂.card=Fintype.card {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}:=by
    rw [hs2]
    simpa only [Fintype.card_coe] using (Fintype.card_congr
      (secondSumIndexEquiv (A:=retainedMarkedIndex π d σ false r Jret w)
        (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))).symm
  have hcard:=actual_residual_size_lower data
  rw [hc,hd',h1,h2,←Fintype.card_sum] at hcard
  have hcardR:(n:ℝ)≤(data.remaining.card:ℝ)+
      ((data.t.biUnion (fun j=>(data.C j).support.toFinset)).card:ℝ)+
      (((m+1)*d-1:ℕ):ℝ)*Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret w):=by
    have hcard':n≤data.remaining.card+(data.t.biUnion (fun j=>(data.C j).support.toFinset)).card+
        ((m+1)*d-1)*Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret w):=by
      simpa only [Fintype.card_fin,retainedAndRawIntervalIndex] using hcard
    exact_mod_cast hcard'
  have hm':(((m+1)*d-1:ℕ):ℝ)≤(((m+1:ℕ):ℝ)*d):=by exact_mod_cast (Nat.sub_le ((m+1)*d) 1)
  have hindex:(0:ℝ)≤Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret w):=by positivity
  have hmul:=mul_le_mul_of_nonneg_right hm' hindex
  have hroot:=retained_raw_interval_root_upper_general π d (m+1) hd (by omega) σ r Jret w
    (longAssignedIntervalProbability F hF K m θ w) t hcounts
  have hmass:=long_assigned_sampling_mass_upper (K:=K) hn m hm F hF θ hθ w
  simp only [Fintype.sum_bool] at hmass
  have hmassN:=mul_le_mul_of_nonneg_left hmass (show 0≤(n:ℝ) by positivity)
  push_cast at hroot hmul
  nlinarith
end Oberwolfach
