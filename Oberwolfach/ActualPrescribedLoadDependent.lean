module

public import Oberwolfach.ActualPrescribedMultiplicityDependent
public import Oberwolfach.ActualPrescribedLoadBudget

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- The old-load hypothesis for actual buffered source data, from the one
sampled interval-occupancy bound and the displayed sparse-load margins. -/
theorem actual_prescribed_load_dependent_from_sampled_intervals
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] {J X:U→Type} [∀w,DecidableEq (J w)] [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (π:Equiv.Perm (Fin n)) (d c:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r)
    (F:∀w,SimpleGraph (X w))
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false r Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}) (J:=J w) (F w))
    (ext:∀w,(retainedMarkedIndex π d σ false r Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin (c*d+5)↪X w)
    (ψ:∀w,X w→Fin n)
    (hc:∀w,(data w).c=c) (hd:∀w,(data w).d=d)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hmarker:∀w i (j:Fin (d+1)),bufferedMarker c d (ext w i) j∈(data w).prescribed→
      ψ w (bufferedMarker c d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σ false true r Jret w i))
    (Kbad:SimpleGraph (Fin n)) (Z:U→Finset (Fin n)) (δ m:ℝ)
    (hm:0<m) (hδ:0≤δ) (hU:Fintype.card U≤n)
    (hM:4/m≤δ/4) (hN:4*(n:ℝ)^(3/4:ℝ)≤δ*n/4)
    (hOcc:∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/m+4*(n:ℝ)^(3/4:ℝ))
    (hKbad:∀v,(Kbad.degree v:ℝ)≤δ*n/4)
    (hZ:∀v,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*n/4):
    ∀v,((Finset.univ.filter (fun w=>v∈
      (residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v+((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*n:=by
  have hpres:=actual_prescribed_multiplicity_dependent_le_extended_hubs π d c σ r Jret F data ext ψ hc hd hsupp hmarker
  exact prescribed_image_load_from_interval_budget (fun w=>(data w).remaining) (fun w=>(data w).prescribed) ψ Kbad Z δ m
    hm hδ hU hM hN (fun v=>(hpres v).trans (hOcc v)) hKbad hZ
end Oberwolfach
