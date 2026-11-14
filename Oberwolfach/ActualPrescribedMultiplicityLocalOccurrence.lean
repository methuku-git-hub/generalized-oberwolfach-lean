module

public import Oberwolfach.ActualPrescribedMultiplicityBoundOn

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_multiplicity_on_from_local_occurrence
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
      4*(H.card:ℝ)/M+4*(A.card:ℝ)^(3/4:ℝ)):
    ∀v∈A,((H.filter (fun w=>v∈
      (residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ) ≤
      4*(H.card:ℝ)/M+4*(A.card:ℝ)^(3/4:ℝ):=by
  intro v hv
  exact (actual_prescribed_multiplicity_on_le_extended_hubs π d c σ r Jret F data ext ψ H hc hd hsupp hmarker v).trans (hraw v hv)
end Oberwolfach
