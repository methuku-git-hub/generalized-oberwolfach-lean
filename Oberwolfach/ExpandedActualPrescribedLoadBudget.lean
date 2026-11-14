module

public import Oberwolfach.ActualPrescribedLoadBudget
public import Oberwolfach.MarkedExpandedActualSample

@[expose] public section
/-! Apply the old prescribed-image load bound to the retained expanded sample,
using the same interval occupancy that the matching event supplies. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance expandedPrescribedFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem actual_prescribed_load_from_expanded_sample
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    {J:U→Type} [∀w,DecidableEq (J w)]
    (π:Equiv.Perm (Fin n)) (d c:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d):
    let σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool:=fun e=>z.1 (Sum.inr e)
    let r:=startRetentionMinimum (rawStartHubSet π d σ false)
    ∀    (F:U→SimpleGraph (Fin n))
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false r z.2 w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}) (J:=J w) (F w))
    (ext:∀w,(retainedMarkedIndex π d σ false r z.2 w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin (c*d+5)↪Fin n)
    (ψ:∀w,Fin n→Fin n)
    (hc:∀w,(data w).c=c) (hd:∀w,(data w).d=d)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hmarker:∀w i (j:Fin (d+1)),bufferedMarker c d (ext w i) j∈(data w).prescribed→
      ψ w (bufferedMarker c d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σ false true r z.2 w i))
    (Kbad:SimpleGraph (Fin n)) (Z:U→Finset (Fin n)) (δ m:ℝ)
    (hm:0<m) (hδ:0≤δ) (hU:Fintype.card U≤n)
    (hM:4/m≤δ/4) (hN:4*(n:ℝ)^(3/4:ℝ)≤δ*n/4)
    (hOcc:∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/m+4*(n:ℝ)^(3/4:ℝ))
    (hKbad:∀v,(Kbad.degree v:ℝ)≤δ*n/4)
    (hZ:∀v,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*n/4),
    ∀v,((Finset.univ.filter (fun w=>v∈
      (residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v+((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*n := by
  have hdec : (Classical.decEq (Fin n)) = instDecidableEqFin n := Subsingleton.elim _ _
  have hGeneral := @actual_prescribed_load_from_sampled_intervals n U inferInstance inferInstance J inferInstance
  rw [←hdec] at hGeneral
  dsimp only
  intro F data ext ψ hc hd hsupp hmarker Kbad Z δ m hm hδ hU hM hN hOcc hKbad hZ
  exact hGeneral π d c (fun e=>z.1 (Sum.inr e))
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 F data ext ψ
    hc hd hsupp hmarker Kbad Z δ m hm hδ hU hM hN hOcc hKbad hZ
end Oberwolfach
