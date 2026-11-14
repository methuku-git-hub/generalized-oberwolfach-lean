module

public import Oberwolfach.OrdinarySampleProfileTriangleSeparatedSpokeCut
public import Oberwolfach.OrdinaryInducedRimCutFromSample

@[expose] public section
/-! Both inner correction cuts are supplied from the original sample and
    cleanup profile; the rim matrix-cut event remains an explicit input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sample_profile_triangle_separated_both_cuts
    (ω h δ ξ:ℝ) (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4)
    (hξ:0<ξ) (hξh:ξ≤h/100):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀η:ℝ,0≤η→η≤η₀→
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U]
      (Q P F:SimpleGraph V) (H:V→U→Prop) (I T:Finset V) (B W:Finset U),T⊆I→W⊆B→
      n₀≤I.card→ω*I.card≤B.card→B.card≤I.card→
      (T.card:ℝ)≤h*I.card→(W.card:ℝ)≤h*B.card→
    ∀(π:Equiv.Perm V) (d:ℕ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
      (a b p γ L Lbase pR pH density tR tH e Ledit βe βh εcut ζcut ζrim href ηrow θ ρ ρhub εTri ωparent:ℝ)
      (Dcut Dmax:ℕ) (s:U→Color→ℝ)
    (ha:0≤a) (hb:0≤b) (hγ:0≤γ)
    (hLV:6*b≤p^6*γ/4) (hLU:6*b≤(p^6*γ/4)*ωparent)
    (hIscale:b≤p^6*γ/8) (hJscale:b≤(p^6*γ/8)*ωparent)
    (hbudget:b+12*a≤ρhub) (hcap:3*b+24*a≤ρ/2) (hθscale:b≤θ)
    (hconst:((Dmax:ℝ)+2*(3*d:ℕ))≤ρ*Fintype.card V/2)
    (hBcard:(B.card:ℝ)≤b*Fintype.card V)
    (event:OrdinaryTriangleSeparatedCoverEvent P F π d Dmax B a p γ ρhub pR pH ηrow θ ρ j raw)
    (hNparent:0<Fintype.card V) (hωparent:0<ωparent) (hpReserve:0<p) (hηrow:0≤ηrow) (hεTri:0≤εTri)
    (hpR0:0≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hBsize:ωparent*Fintype.card V≤((Finset.univ\B).card:ℝ)) (hUlower:ωparent*Fintype.card V≤Fintype.card U)
    (Dmean:ℝ) (hreg:∀v,|(P.degree v:ℝ)-Dmean|≤εTri*Fintype.card V)
    (hidentity:pR*Dmean=2*Fintype.card U*pH) (hbalance:εTri+2*b≤2*ωparent*p*ηrow),
      OrdinaryCleanupParentProfiles P Q F H π d I B pR pH density tR tH Ledit βe βh s j raw→
      0<I.card→0<B.card→0<pH→pH≤1→0≤εcut→0≤ζcut→δ≤pH/16→ζcut≤pH^2/128→2*h≤pH/8→
      0≤ζrim→Ledit≤ζrim*I.card→2*h≤href-ζrim→
      (∀S T:Finset I,(1-2*δ)*I.card<(S.card:ℝ)+T.card→
        href*I.card*min (S.card:ℝ) T.card≤
          (matrixCut (fun x y:I=>sampledOrientation (rawWheelGraph P raw) coins x.val y.val) S T:ℝ))→
      (∀v,F.degree v≤Dcut)→tH+2*Ledit≤εcut*B.card→
      tH+Ledit≤pH*B.card/2→tR+Ledit≤pH*I.card/2→
      3*εcut*(I.card:ℝ)^2*(B.card:ℝ)^2+((Dcut+1:ℕ):ℝ)*I.card*(B.card:ℝ)^2≤(ζcut*I.card*B.card)^2→
      0≤Ledit→
      (∀v:I,|(((Q.induce (I:Set V)).degree v):ℝ)-2*(Finset.univ.filter (fun u:B=>H v.val u.val)).card|≤η*I.card)→Ledit≤Lbase→
      0<a→a≤1→80*ξ≤a^2→Fintype.card U≤Fintype.card V→4≤a^2*Fintype.card V→
      (I.card:ℝ)≤b*Fintype.card V→(T.card:ℝ)≤b*Fintype.card V→
      (2*W.card:ℝ)≤L→0≤L→L≤b*Fintype.card V→
      (∀v,(F.degree v:ℝ)≤L)→Q≤P→Lbase+I.card≤L→Lbase+B.card≤L→
      (∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card)→
      (∀u∈W,3∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∃(D:SimpleGraph V) (J:V→U→Prop),
      D≤spanningRestriction Q I ∧ (∀v∈T,∀w∈T,¬D.Adj v w) ∧
      (∀v u,J v u→(H v u∧v∈I∧u∈B)∧¬(v∈T∧u∈W)) ∧
      (∀v,((spanningRestriction Q I)\D).degree v=
        2*(Finset.univ.filter (fun u=>(H v u∧v∈I∧u∈B)∧¬J v u)).card) ∧
      (∀u,3∣(Finset.univ.filter (fun v=>(H v u∧v∈I∧u∈B)∧¬J v u)).card) ∧
      (∀x:V⊕U,((ordinaryPhysicalGraph D J).degree x:ℝ)≤10*ξ*I.card) ∧
      let ReservedRim:=ordinaryRimRootStar ((spanningRestriction Q I)\D) T;
      let ReservedSpokes:=ordinarySpokeRootStar (fun v u=>(H v u∧v∈I∧u∈B)∧¬J v u) T W;
      let Qout:=Q\ReservedRim;
      let Hout:=fun v u=>H v u∧¬ReservedSpokes v u;
      let E:=(ordinaryHostResources D J).filter (ordinaryResourceTouchesRoots T W);
      ∃M:Finset (OrdinaryWheel Qout F Hout 3),
        (∀A∈M,∀B'∈M,A≠B'→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B')) ∧
        M.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Qout I)
          (fun v u=>Hout v u∧v∈I∧u∈B)=E ∧
        (∀v∈T,∀w,(ordinaryWheelRimGraph M).Adj v w↔Qout.Adj v w) ∧
        (∀v∈T,∀u,ordinaryPackingSpokes M v u↔Hout v u) ∧
        (∀u∈W,∀v,ordinaryPackingSpokes M v u↔Hout v u) ∧
      (∀v∉T,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inl v):ℝ)≤
        18*a*Fintype.card V+3*((W.card:ℝ)+T.card)) ∧
      (∀u∉W,((ordinaryPhysicalGraph (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M)).degree (Sum.inr u):ℝ)≤
        9*a*Fintype.card V+3*(T.card:ℝ)) ∧
      Disjoint (M.biUnion ordinaryWheelResources)
        (ordinaryHostResources (spanningRestriction Q T) (fun v u=>H v u∧v∈T∧u∈W)) :=by
  obtain ⟨η₀,hη₀,n₀,hmain⟩:=ordinary_sample_profile_triangle_separated_spoke_cut ω h δ ξ hω hh hδ hδsmall hξ hξh
  refine ⟨η₀,hη₀,n₀,?_⟩
  intro η hη hη0 V U Γ Color _ _ _ _ _ _ Q P F H I T B W hTI hWB hn hωI hBI hTsize hWsize
    π d j raw coins a b p γ L Lbase pR pH density tR tH e Ledit βe βh εcut ζcut ζrim href ηrow θ ρ ρhub εTri ωparent Dcut Dmax s
    ha hb hγ hLV hLU hIscale hJscale hbudget hcap hθscale hconst hBcard event hNparent hωparent hpReserve hηrow hεTri
    hpR0 hpR1 hpH hpH1 hBsize hUlower Dmean hreg hidentity hbalance profile
    hIpos hBpos hp hp1 hεcut hζcut hδcut hζsmall hhcut hζrim hrimscale hrimmargin hmat
    hFcut herror hrowMin hcolMin hcutbudget hLedit hbal hedit haPos ha1 hξsmall hU hnlarge
    hI hT hW hL hLsmall hF hQ hbudgetI hbudgetB hQbal hHdiv
  obtain ⟨R,horient,hcutR⟩:=ordinary_induced_rim_cut_from_sample_and_edits (rawWheelGraph P raw) Q I coins δ href ζrim Ledit h
    hIpos hζrim hrimscale hrimmargin profile.rim_edit hmat
  exact hmain η hη hη0 V U Γ Color Q P F H I T B W hTI hWB hn hωI hBI hTsize hWsize R horient hcutR
    π d j raw a b p γ L Lbase pR pH density tR tH e Ledit βe βh εcut ζcut ηrow θ ρ ρhub εTri ωparent Dcut Dmax s
    ha hb hγ hLV hLU hIscale hJscale hbudget hcap hθscale hconst hBcard event hNparent hωparent hpReserve hηrow hεTri
    hpR0 hpR1 hpH hpH1 hBsize hUlower Dmean hreg hidentity hbalance profile hIpos hBpos hp hp1
    hεcut hζcut hδcut hζsmall hhcut hFcut herror hrowMin hcolMin hcutbudget hLedit hbal hedit
    haPos ha1 hξsmall hU hnlarge hI hT hW hL hLsmall hF hQ hbudgetI hbudgetB hQbal hHdiv
end Oberwolfach
