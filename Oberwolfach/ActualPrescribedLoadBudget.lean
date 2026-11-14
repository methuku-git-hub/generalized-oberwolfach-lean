module

public import Oberwolfach.ActualPrescribedMultiplicityBound

@[expose] public section
/-! The sampled interval occupancy, sparse bad graph and absorber-target load
combine to give the exact old prescribed-image multiplicity hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_image_load_from_interval_budget
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (remaining prescribed:∀w,Finset (X w)) (ψ:∀w,X w→Fin n)
    (Kbad:SimpleGraph (Fin n)) (Z:U→Finset (Fin n)) (δ m:ℝ)
    (hm:0<m) (hδ:0≤δ) (hU:Fintype.card U≤n)
    (hM:4/m≤δ/4) (hN:4*(n:ℝ)^(3/4:ℝ)≤δ*n/4)
    (hPrescribed:∀v,((Finset.univ.filter (fun w=>v∈
      (residualSubtypeSet (remaining w) (prescribed w)).image (fun x=>ψ w x.1))).card:ℝ)≤
      4*(Fintype.card U:ℝ)/m+4*(n:ℝ)^(3/4:ℝ))
    (hKbad:∀v,(Kbad.degree v:ℝ)≤δ*n/4)
    (hZ:∀v,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*n/4):
    ∀v,((Finset.univ.filter (fun w=>v∈
      (residualSubtypeSet (remaining w) (prescribed w)).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v+((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*n:=by
  have hUR:(Fintype.card U:ℝ)≤n:=by exact_mod_cast hU
  have hterm:4*(Fintype.card U:ℝ)/m≤δ*n/4:=by
    have h1:=div_le_div_of_nonneg_right hUR hm.le
    have h2:=mul_le_mul_of_nonneg_left h1 (show (0:ℝ)≤4 by norm_num)
    have h3:=mul_le_mul_of_nonneg_right hM (show (0:ℝ)≤n by positivity)
    calc
      _ = 4*((Fintype.card U:ℝ)/m):=by ring
      _ ≤ 4*((n:ℝ)/m):=h2
      _ = (4/m)*(n:ℝ):=by ring
      _ ≤ (δ/4)*(n:ℝ):=h3
      _ = _:=by ring
  intro v
  linarith [hPrescribed v,hKbad v,hZ v]

/-- The old-load hypothesis for actual buffered source data, from the one
sampled interval-occupancy bound and the displayed sparse-load margins. -/
theorem actual_prescribed_load_from_sampled_intervals
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] {J:U→Type} [∀w,DecidableEq (J w)]
    (π:Equiv.Perm (Fin n)) (d c:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r)
    (F:U→SimpleGraph (Fin n))
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false r Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}) (J:=J w) (F w))
    (ext:∀w,(retainedMarkedIndex π d σ false r Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin (c*d+5)↪Fin n)
    (ψ:∀w,Fin n→Fin n)
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
  have hpres:=actual_prescribed_multiplicity_le_extended_hubs π d c σ r Jret F data ext ψ hc hd hsupp hmarker
  exact prescribed_image_load_from_interval_budget (fun w=>(data w).remaining) (fun w=>(data w).prescribed) ψ Kbad Z δ m
    hm hδ hU hM hN (fun v=>(hpres v).trans (hOcc v)) hKbad hZ
end Oberwolfach
