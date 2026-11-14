module

public import Oberwolfach.ActualPrescribedMultiplicityLocalOccurrence

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_load_on_from_local_occurrence
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] {J:U→Type} [∀w,DecidableEq (J w)]
    (π:Equiv.Perm (Fin n)) (d c:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r)
    (F:U→SimpleGraph (Fin n))
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false r Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}) (J:=J w) (F w))
    (ext:∀w,(retainedMarkedIndex π d σ false r Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin (c*d+5)↪Fin n)
    (ψ:∀w,Fin n→Fin n) (H:Finset U)
    (hc:∀w,(data w).c=c) (hd:∀w,(data w).d=d)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hmarker:∀w i (j:Fin (d+1)),bufferedMarker c d (ext w i) j∈(data w).prescribed→
      ψ w (bufferedMarker c d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σ false true r Jret w i))
    (A:Finset (Fin n)) (M:ℝ)
    (hraw:∀v∈A,((rawIntervalExtendedAnyHubSet π d σ v ∩ H).card:ℝ) ≤
      4*(H.card:ℝ)/M+4*(A.card:ℝ)^(3/4:ℝ))
    (Kbad:SimpleGraph (Fin n)) (Z:U→Finset (Fin n)) (δ:ℝ)
    (hMpos:0<M) (hM:4/M≤δ/4) (hδ:0≤δ) (hH:(H.card:ℝ)≤(A.card:ℝ))
    (hN:4*(A.card:ℝ)^(3/4:ℝ)≤δ*(A.card:ℝ)/4)
    (hKbad:∀v∈A,(Kbad.degree v:ℝ)≤δ*(A.card:ℝ)/4)
    (hZ:∀v∈A,((H.filter (fun w=>v∈Z w)).card:ℝ)≤δ*(A.card:ℝ)/4):
    ∀v∈A,((H.filter (fun w=>v∈
      (residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ) +
      Kbad.degree v+((H.filter (fun w=>v∈Z w)).card:ℝ) ≤ δ*(A.card:ℝ):=by
  intro v hv
  have hpres:=actual_prescribed_multiplicity_on_from_local_occurrence π d c σ r Jret F data ext ψ H hc hd hsupp hmarker A M hraw v hv
  have hM':4*(H.card:ℝ)/M≤δ*(A.card:ℝ)/4:=by
    have hh:=mul_le_mul_of_nonneg_left hH (show (0:ℝ)≤4/M by positivity)
    have hk:=mul_le_mul_of_nonneg_right hM (show (0:ℝ)≤(A.card:ℝ) by positivity)
    calc
      4*(H.card:ℝ)/M = (4/M)*(H.card:ℝ) := by ring
      _ ≤ (4/M)*(A.card:ℝ) := hh
      _ ≤ (δ/4)*(A.card:ℝ) := hk
      _ = δ*(A.card:ℝ)/4 := by ring
  linarith only [hpres,hM',hN,hKbad v hv,hZ v hv]
end Oberwolfach
