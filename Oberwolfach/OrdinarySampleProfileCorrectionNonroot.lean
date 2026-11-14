module

public import Oberwolfach.OrdinaryConstructedCorrectionNonrootProtected
public import Oberwolfach.OrdinaryInducedCorrectionBalanceFromSample
public import Oberwolfach.OrdinaryCorrectionStarScaledBudgets

@[expose] public section
/-! The sampled cleanup profile supplies the correction balance, edit
    bounds and numerical ceiling budgets for the protected triangle cover. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sample_profile_constructs_correction_nonroot
    (m K:ℕ) (hm:3≤m) (ω h δ ξ:ℝ) (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4)
    (hξ:0<ξ) (hξh:ξ≤h/100):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀η:ℝ,0≤η→η≤η₀→
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U]
      (Q P F:SimpleGraph V) (H:V→U→Prop) (I T:Finset V) (B W:Finset U),T⊆I→W⊆B→
      n₀≤I.card→ω*I.card≤B.card→B.card≤I.card→
      (T.card:ℝ)≤h*I.card→(W.card:ℝ)≤h*B.card→
    ∀(R:I→I→Prop),
      (∀x y,relationMultiplicity R x y+relationMultiplicity R y x=
        if (Q.induce (I:Set V)).Adj x y then 1 else 0)→
      BipartiteLargeCut (relationMultiplicity R) δ (2*h)→
      BipartiteLargeCut (relationMultiplicity (fun v:I=>fun u:B=>H v.val u.val)) δ (2*h)→
    ∀(π:Equiv.Perm V) (d:ℕ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
      (a aLoad ρ θ L Lbase pR pH density tR tH e Ledit βe βh:ℝ) (s:U→Color→ℝ),
      OrdinaryCleanupParentProfiles P Q F H π d I B pR pH density tR tH Ledit βe βh s j raw→
      0≤tR→0≤tH→0≤e→0≤Ledit→
      (∀v,|pR*(P.neighborFinset v∩I).card-2*pH*B.card|≤e)→
      e+tR+2*tH+3*Ledit≤η*I.card→Ledit≤Lbase→
      OrdinaryDeepCoverSeparateLoadEvent m K a aLoad ρ θ P F B π d j raw→
      0<aLoad→aLoad≤1→80*ξ≤aLoad^2→Fintype.card U≤Fintype.card V→4≤aLoad^2*Fintype.card V→
      (I.card:ℝ)≤a*Fintype.card V→(T.card:ℝ)≤θ*Fintype.card V→
      (2*W.card:ℝ)≤L→0≤L→L≤ρ*Fintype.card V→
      (∀v,(F.degree v:ℝ)≤L)→Q≤P→Lbase+I.card≤L→Lbase+B.card≤L→
      (∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card)→
      (∀u∈W,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∃(D:SimpleGraph V) (J:V→U→Prop),
      D≤spanningRestriction Q I ∧ (∀v∈T,∀w∈T,¬D.Adj v w) ∧
      (∀v u,J v u→(H v u∧v∈I∧u∈B)∧¬(v∈T∧u∈W)) ∧
      (∀v,((spanningRestriction Q I)\D).degree v=
        2*(Finset.univ.filter (fun u=>(H v u∧v∈I∧u∈B)∧¬J v u)).card) ∧
      (∀u,(m+1)∣(Finset.univ.filter (fun v=>(H v u∧v∈I∧u∈B)∧¬J v u)).card) ∧
      (∀x:V⊕U,((ordinaryPhysicalGraph D J).degree x:ℝ)≤10*ξ*I.card) ∧
      let ReservedRim:=ordinaryRimRootStar ((spanningRestriction Q I)\D) T;
      let ReservedSpokes:=ordinarySpokeRootStar (fun v u=>(H v u∧v∈I∧u∈B)∧¬J v u) T W;
      let Qout:=Q\ReservedRim;
      let Hout:=fun v u=>H v u∧¬ReservedSpokes v u;
      let E:=(ordinaryHostResources D J).filter (ordinaryResourceTouchesRoots T W);
      ∃M:Finset (OrdinaryWheel Qout F Hout (m+1)),
        (∀A∈M,∀B'∈M,A≠B'→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B')) ∧
        M.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Qout I)
          (fun v u=>Hout v u∧v∈I∧u∈B)=E ∧
        (∀v∈T,∀w,(ordinaryWheelRimGraph M).Adj v w↔Qout.Adj v w) ∧
        (∀v∈T,∀u,ordinaryPackingSpokes M v u↔Hout v u) ∧
        (∀u∈W,∀v,ordinaryPackingSpokes M v u↔Hout v u) ∧
      (∀v∉T,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inl v):ℝ)≤
        18*aLoad*Fintype.card V+3*((W.card:ℝ)+(K+1)*T.card)) ∧
      (∀u∉W,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inr u):ℝ)≤
        3*aLoad*Fintype.card V*(m+1)+(T.card:ℝ)*(m+1)) ∧
      Disjoint (M.biUnion ordinaryWheelResources)
        (ordinaryHostResources (spanningRestriction Q T) (fun v u=>H v u∧v∈T∧u∈W)) :=by
  obtain ⟨η₀,hη₀,n₀,hmain⟩:=ordinary_constructed_correction_nonroot_protected m K hm ω h δ ξ hω hh hδ hδsmall hξ hξh
  refine ⟨η₀,hη₀,n₀,?_⟩
  intro η hη hη0 V U Γ Color _ _ _ _ _ _ Q P F H I T B W hTI hWB hn hωI hBI hTsize hWsize
    R horient hcutR hcutH π d j raw a aLoad ρ θ L Lbase pR pH density tR tH e Ledit βe βh s profile
    htR htH he hLedit hparent hmargin hedit event ha ha1 hξsmall hU hnlarge hI hT hW hL hLsmall hF hQ hbudgetI hbudgetB hQbal hHdiv
  have hbal:=ordinary_induced_correction_balance_from_sample P Q F H π d I B pR pH density tR tH e Ledit βe βh η
    htR htH he hLedit s j raw profile hparent hmargin
  have hbudget:=ordinary_correction_star_scaled_budgets (Fintype.card V) (Fintype.card U) I.card aLoad ξ
    ha ha1 hξ hξsmall hU (Finset.card_le_univ I) hnlarge
  have hEscale:((Fintype.card (V⊕U)*⌈10*ξ*I.card⌉₊:ℕ):ℝ)≤aLoad^2*(Fintype.card V:ℝ)^2:=by
    simpa only [Fintype.card_sum] using hbudget.2
  have hQP:Q≤P\F:=by
    intro v w hvw
    refine ⟨hQ hvw,?_⟩
    intro hf
    exact (disjoint_iff_inf_le.mp profile.forbidden_disjoint) ⟨hvw,hf⟩
  apply hmain η hη hη0 V U Γ Color Q P F H I T B W hTI hWB hn hωI hBI hTsize hWsize
    R horient hcutR hcutH
    (by intro v;convert hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    π d j raw a aLoad ρ θ L Lbase event hbudget.1 hEscale hI hT hW hL hLsmall hF hQP hbudgetI hbudgetB
    (by intro v;exact (profile.rim_edit v).trans hedit)
    (by intro v;exact (profile.spoke_row_edit v).trans hedit)
    (by intro u;exact (profile.spoke_column_edit u).trans hedit)
    hQbal hHdiv
end Oberwolfach
