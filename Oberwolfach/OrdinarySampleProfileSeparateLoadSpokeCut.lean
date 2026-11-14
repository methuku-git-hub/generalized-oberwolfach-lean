module

public import Oberwolfach.OrdinarySampleProfileCorrectionSeparateLoad
public import Oberwolfach.OrdinaryCleanupInnerSpokeCut

@[expose] public section
/-! The sampled profile now supplies the induced spoke cut as well as the
    balance and edit bounds in the protected triangle construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sample_profile_separate_load_with_spoke_cut
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
    ∀(π:Equiv.Perm V) (d:ℕ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
      (a aLoad ρ θ L Lbase pR pH density tR tH e Ledit βe βh εcut ζcut:ℝ) (Dcut:ℕ) (s:U→Color→ℝ),
      OrdinaryCleanupParentProfiles P Q F H π d I B pR pH density tR tH Ledit βe βh s j raw→
      0<I.card→0<B.card→0<pH→pH≤1→0≤εcut→0≤ζcut→δ≤pH/16→ζcut≤pH^2/128→2*h≤pH/8→
      (∀v,F.degree v≤Dcut)→tH+2*Ledit≤εcut*B.card→
      tH+Ledit≤pH*B.card/2→tR+Ledit≤pH*I.card/2→
      3*εcut*(I.card:ℝ)^2*(B.card:ℝ)^2+((Dcut+1:ℕ):ℝ)*I.card*(B.card:ℝ)^2≤(ζcut*I.card*B.card)^2→
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
      (∀v∉I,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inl v):ℝ)≤
        18*aLoad*Fintype.card V+3*((W.card:ℝ)+(K+1)*T.card)) ∧
      (∀u∉B,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inr u):ℝ)≤
        3*aLoad*Fintype.card V*(m+1)+(T.card:ℝ)*(m+1)) ∧
      Disjoint (M.biUnion ordinaryWheelResources)
        (ordinaryHostResources (spanningRestriction Q T) (fun v u=>H v u∧v∈T∧u∈W)) :=by
  obtain ⟨η₀,hη₀,n₀,hmain⟩:=ordinary_sample_profile_constructs_correction_separate_load m K hm ω h δ ξ hω hh hδ hδsmall hξ hξh
  refine ⟨η₀,hη₀,n₀,?_⟩
  intro η hη hη0 V U Γ Color _ _ _ _ _ _ Q P F H I T B W hTI hWB hn hωI hBI hTsize hWsize
    R horient hcutR π d j raw a aLoad ρ θ L Lbase pR pH density tR tH e Ledit βe βh εcut ζcut Dcut s profile
    hIpos hBpos hp hp1 hεcut hζcut hδcut hζsmall hhcut hFcut herror hrowMin hcolMin hcutbudget
    htR htH he hLedit hparent hmargin hedit event ha ha1 hξsmall hU hnlarge hI hT hW hL hLsmall hF hQ hbudgetI hbudgetB hQbal hHdiv
  have hspoke:=ordinary_cleanup_inner_spoke_cut P Q F H π d I B pR pH density tR tH Ledit βe βh εcut ζcut δ h Dcut
    s j raw profile hIpos hBpos hp hp1 hεcut hζcut hδcut hζsmall hhcut hLedit hFcut herror hrowMin hcolMin hcutbudget
  exact hmain η hη hη0 V U Γ Color Q P F H I T B W hTI hWB hn hωI hBI hTsize hWsize R horient hcutR hspoke
    π d j raw a aLoad ρ θ L Lbase pR pH density tR tH e Ledit βe βh s profile htR htH he hLedit hparent hmargin hedit
    event ha ha1 hξsmall hU hnlarge hI hT hW hL hLsmall hF hQ hbudgetI hbudgetB hQbal hHdiv
end Oberwolfach
