module

public import Oberwolfach.ActualResidualSizeLower
public import Oberwolfach.RetainedRawIntervalRootUpper
public import Oberwolfach.ResidualSmallnessScale

@[expose] public section
/-! A checked diagnostic for the no-ordinary-cycle case: the current sampling
leaves a residual on the linear θ scale, while the existing generic residual
embedding theorem asks for the quadratic scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_lower_from_start_budget
    {n:ℕ} {U J:Type} [Fintype U] [DecidableEq U] [DecidableEq J]
    (π:Equiv.Perm (Fin n)) (d c:ℕ) (hd:0<d) (hc:0<c)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (r:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r) (w:U)
    {F:SimpleGraph (Fin n)}
    (data:ActualResidualData (K:=retainedAndRawIntervalIndex π d σ false true r Jret w) (J:=J) F)
    (hC:(data.t.biUnion (fun j=>(data.C j).support.toFinset)).card=0)
    (hc':data.c=c) (hd':data.d=d) (hs1:data.s₁=firstSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (hs2:data.s₂=secondSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (q:Bool→ℝ) (θ t:ℝ) (hqsum:q false+q true=(1-θ)/(c:ℝ))
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-(n:ℝ)*q g/(d:ℝ)|<t/(d:ℝ)):
    θ*(n:ℝ)-2*(c:ℝ)*t≤(data.remaining.card:ℝ):=by
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
  rw [hC,hc',hd',h1,h2,←Fintype.card_sum] at hcard
  have hcardR:(n:ℝ)≤(data.remaining.card:ℝ)+(((c*d-1:ℕ):ℝ))*
      (Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret w):ℝ):=by
    have hcard':n≤data.remaining.card+(c*d-1)*
        Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret w):=by
      simpa only [Fintype.card_fin,Nat.add_zero,retainedAndRawIntervalIndex] using hcard
    exact_mod_cast hcard'
  have hm:((c*d-1:ℕ):ℝ)≤(c:ℝ)*d:=by
    exact_mod_cast (Nat.sub_le (c*d) 1)
  have hindex:(0:ℝ)≤Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret w):=by positivity
  have hm' := mul_le_mul_of_nonneg_right hm hindex
  have hroot:=retained_raw_interval_root_upper_from_counts π d c hd hc σ r Jret w q θ t hqsum hcounts
  nlinarith

theorem actual_residual_incompatible_with_quadratic_scale
    {n:ℕ} {U J:Type} [Fintype U] [DecidableEq U] [DecidableEq J]
    (π:Equiv.Perm (Fin n)) (d c:ℕ) (hd:0<d) (hc:0<c)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (r:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r) (w:U)
    {F:SimpleGraph (Fin n)}
    (data:ActualResidualData (K:=retainedAndRawIntervalIndex π d σ false true r Jret w) (J:=J) F)
    (hC:(data.t.biUnion (fun j=>(data.C j).support.toFinset)).card=0)
    (hc':data.c=c) (hd':data.d=d) (hs1:data.s₁=firstSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (hs2:data.s₂=secondSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (q:Bool→ℝ) (θ t β δ:ℝ) (hθ:0<θ) (hθ1:θ≤1) (hβ:0≤β) (hβθ:β≤θ)
    (hqsum:q false+q true=(1-θ)/(c:ℝ))
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-(n:ℝ)*q g/(d:ℝ)|<t/(d:ℝ))
    (hn:0<n) (herror:4*(c:ℝ)*t≤θ*n) (hδ:δ≤(β/100)^2):
    ¬((data.remaining.card:ℝ)≤δ*n):=by
  intro hsmall
  have hlower:=actual_residual_lower_from_start_budget π d c hd hc σ r Jret w data hC hc' hd' hs1 hs2 q θ t hqsum hcounts
  have hscale:δ≤θ^2/10000:=(residual_smallness_forces_quadratic_scale θ β δ hθ hθ1 hβ hβθ hδ).1
  have hθsq:θ^2≤θ:=by nlinarith
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  nlinarith
end Oberwolfach
