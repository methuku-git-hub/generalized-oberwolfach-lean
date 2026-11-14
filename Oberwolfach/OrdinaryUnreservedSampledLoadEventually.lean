module

public import Oberwolfach.OrdinaryUnreservedPrescribedLoadBudget
public import Oberwolfach.OrdinaryOccupancyMarginsEventually

@[expose] public section
/-! The actual unreserved prescribed-image load and a sparse bad graph fit
the placement budget on the sampled occupancy event, for large order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_sampled_load_eventually (δ:ℝ) (hδ:0<δ):
    ∃m₀ N:ℕ,7≤m₀ ∧ ∀m≥m₀,∀{n:ℕ},N≤n→∀{U:Type} [Fintype U] [DecidableEq U]
      {J:U→Type} [∀w,DecidableEq (J w)]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r)
    (F:U→SimpleGraph (Fin n)) (Cres:∀w,Finset (F w).ConnectedComponent),
    let X:=fun w=>{x:Fin n // (F w).connectedComponentMk x∉Cres w}
    let G:=fun w=>(F w).induce {x | (F w).connectedComponentMk x∉Cres w};
    ∀(data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d σ false r Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}) (J:=J w) (G w))
    (ext:∀w,(retainedMarkedIndex π d σ false r Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin ((m+1)*d+5)↪X w)
    (ψ:∀w,X w→Fin n)
    (hc:∀w,(data w).c=m+1) (hd:∀w,(data w).d=d)
    (hsupp:∀w i,((data w).P i).support=List.ofFn (ext w i))
    (hmarker:∀w i (j:Fin (d+1)),bufferedMarker (m+1) d (ext w i) j∈(data w).prescribed→
      ψ w (bufferedMarker (m+1) d (ext w i) j)=(π^j.val) (retainedAndRawIntervalRoot π d σ false true r Jret w i))
    (Kbad:SimpleGraph (Fin n)) (b:ℝ) (hb:0≤b) (hbδ:b≤δ/4) (hU:Fintype.card U≤n)
    (hOcc:∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/((m:ℝ)+1)+4*(n:ℝ)^(3/4:ℝ))
    (hKbad:∀v,(Kbad.degree v:ℝ)≤b*n),
    ∀v,((Finset.univ.filter (fun w=>v∈
      (residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v≤δ*n:=by
  obtain ⟨m₀,N,hm₀,hMargins⟩:=ordinary_occupancy_margins_eventually δ hδ
  refine ⟨m₀,N,hm₀,?_⟩
  intro m hm n hn U _ _ J _ π d σ r Jret F Cres X G data ext ψ hc hd hsupp hmarker Kbad b hb hbδ hU hOcc hKbad
  obtain ⟨hmpos,hmarg,hpow⟩:=hMargins m hm n hn
  have hdeg:∀v,(Kbad.degree v:ℝ)≤δ*n/4:=by
    intro v
    have hh:=mul_le_mul_of_nonneg_right hbδ (show 0≤(n:ℝ) by positivity)
    nlinarith [hKbad v]
  have hZ:∀v,((Finset.univ.filter (fun _w:U=>v∈(∅:Finset (Fin n)))).card:ℝ)≤δ*n/4:=by
    intro v
    simp only [Finset.notMem_empty,Finset.filter_false,Finset.card_empty,Nat.cast_zero]
    positivity
  have hh:=ordinary_unreserved_prescribed_load_with_sparse_budgets π d (m+1) σ r Jret F Cres data ext ψ hc hd hsupp hmarker Kbad
    (fun _=>∅) δ ((m:ℝ)+1) hmpos hδ.le hU hmarg hpow hOcc hdeg hZ
  intro v
  simpa only [Finset.notMem_empty,Finset.filter_false,Finset.card_empty,Nat.cast_zero,add_zero] using hh v
end Oberwolfach
