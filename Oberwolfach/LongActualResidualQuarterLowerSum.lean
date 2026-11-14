module

public import Oberwolfach.ActualResidualSizeLower
public import Oberwolfach.ApproximateSublinearMargin
public import Oberwolfach.LongActualResidualSizeLowerSum
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

theorem long_actual_residual_quarter_lower_from_counts_sum
    (m d:ℕ) (hm:0<m) (hd:0<d) (θ:ℝ) (hθ:0<θ):
    ∃N:ℕ,∀{n K:ℕ} (hnN:N≤n) {U J:Type} [Fintype U] [DecidableEq U] [DecidableEq J]
    (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r) (w:U),
    let Aidx:=retainedMarkedIndex π d σ false r Jret w
    let Bidx:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}
    letI : DecidableEq (Aidx⊕Bidx) := @instDecidableEqSum Aidx Bidx _ _
    ∀(data:ActualResidualData (K:=retainedAndRawIntervalIndex π d σ false true r Jret w) (J:=J) (F w))
    (hc:data.c=m+1) (hd':data.d=d)
    (hs1:data.s₁=firstSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (hs2:data.s₂=secondSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (err:ℝ) (hθ1:θ≤1)
    (herr:err≤(θ/100)*n)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (hC:((data.t.biUnion (fun j=>(data.C j).support.toFinset)).card:ℝ)≤
      (n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w))+err),
    θ*n/4≤(data.remaining.card:ℝ):=by
  let c:ℝ:=(m:ℝ)+1
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (θ/(8*c)) 0 (by positivity)
  refine ⟨N,?_⟩
  intro n K hnN U J _ _ _ hn F hF π σ r Jret w Aidx Bidx data hc' hd' hs1 hs2 err hθ1 herr hcounts hC
  have hroot:=hN n hnN
  have hroot':2*c*(n:ℝ)^(3/4:ℝ)≤(θ/4)*n:=by
    have hh:=mul_le_mul_of_nonneg_left hroot (show 0≤2*c by positivity)
    have heq:2*c*(θ/(8*c)*(n:ℝ))=(θ/4)*n:=by field_simp; ring
    nlinarith [heq]
  have hsize:=long_actual_residual_size_lower_from_counts_sum hn m d hm hd F hF π σ r Jret w data hc' hd' hs1 hs2 θ ((n:ℝ)^(3/4:ℝ)) err hθ1 hcounts hC
  dsimp [c] at hroot'
  nlinarith
end Oberwolfach
