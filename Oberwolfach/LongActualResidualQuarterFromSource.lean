module

public import Oberwolfach.ActualResidualSizeLower
public import Oberwolfach.ApproximateSublinearMargin
public import Oberwolfach.LongActualResidualSizeLower
public import Oberwolfach.LongActualResidualQuarterLower
public import Oberwolfach.ResidualOrdinaryMassFromSourceUpper
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

theorem long_actual_residual_quarter_lower_from_source
    (m d:ℕ) (hm:0<m) (hd:0<d) (θ:ℝ) (hθ:0<θ):
    ∃N:ℕ,∀{n K:ℕ} (hnN:N≤n) {U J:Type} [Fintype U] [DecidableEq U] [DecidableEq J]
    (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r) (w:U)
    (data:ActualResidualData (K:=retainedAndRawIntervalIndex π d σ false true r Jret w) (J:=J) (F w))
    (hc:data.c=m+1) (hd':data.d=d)
    (hs1:data.s₁=firstSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (hs2:data.s₂=secondSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (err:ℝ) (hθ1:θ≤1)
    (herr:err≤(θ/100)*n)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (hEmbed:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset))
    (sourceMass:ℕ) (hcard:data.Cembed.card=sourceMass)
    (hsource:|((sourceMass:ℝ)-(n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w)))|≤err),
    θ*n/4≤(data.remaining.card:ℝ):=by
  obtain ⟨N,hN⟩:=long_actual_residual_quarter_lower_from_counts m d hm hd θ hθ
  refine ⟨N,?_⟩
  intro n K hnN U J _ _ _ hn F hF π σ r Jret w data hc hd' hs1 hs2 err hθ1 herr hcounts hEmbed sourceMass hcard hsource
  have hC:=residual_ordinary_mass_upper_from_source_count data hEmbed sourceMass hcard
    ((n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w))) err hsource
  exact hN hnN hn F hF π σ r Jret w data hc hd' hs1 hs2 err hθ1 herr hcounts hC
end Oberwolfach
