module

public import Oberwolfach.ActualPrescribedLoadBudget
public import Oberwolfach.InnerTargetLoadBudget

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_load_with_inner_target_bounds
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
    (θ η ζ ρ:ℝ) (hθ:0≤θ) (hθδ:10*θ≤δ)
    (hη:η≤θ/4096) (hζ:ζ≤θ/4096) (hρ:ρ≤θ/4096)
    (hZ:∀v,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤(2*θ+η+ζ+ρ)*n):
    ∀v,((Finset.univ.filter (fun w=>v∈
      (residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v+((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*n:=by
  have hcoeff:=inner_target_occurrence_budget θ δ η ζ ρ hθ hθδ hη hζ hρ
  have hZ':∀v,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*n/4:=by
    intro v
    have hh:=mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n)
    linarith [hZ v]
  exact actual_prescribed_load_from_sampled_intervals π d c σ r Jret F data ext ψ hc hd hsupp hmarker Kbad Z δ m hm hδ hU hM hN hOcc hKbad hZ'
end Oberwolfach
