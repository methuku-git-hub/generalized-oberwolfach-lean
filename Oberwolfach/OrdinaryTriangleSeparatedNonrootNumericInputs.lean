module

public import Oberwolfach.OrdinaryNonrootCoverNumericInputs
public import Oberwolfach.OrdinarySampleProfileTriangleSeparatedBothCuts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem ordinary_triangle_separated_nonroot_cover_from_numeric_inputs
    (ω ε δcut ξ:ℝ) (hω:0<ω) (hε:0<ε) (hδ:0<δcut) (hδsmall:δcut<1/4)
    (hξ:0<ξ) (hξε:ξ≤ε/100):
    ∃η₀:ℝ,0<η₀ ∧ ∃n₀:ℕ,∀η:ℝ,0≤η→η≤η₀→
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U]
      (Q P F:SimpleGraph V) (H:V→U→Prop) (I T:Finset V) (B W:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
      (a b p γ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar ηrow θ ρ ρhub εTri ωparent:ℝ)
      (Dmax:ℕ) (s:U→Color→ℝ)
      (ha:0≤a) (hb:0≤b) (hγ:0≤γ)
      (hLV:6*b≤p^6*γ/4) (hLU:6*b≤(p^6*γ/4)*ωparent)
      (hIscale:b≤p^6*γ/8) (hJscale:b≤(p^6*γ/8)*ωparent)
      (hbudget:b+12*a≤ρhub) (hcap:3*b+24*a≤ρ/2) (hθscale:b≤θ)
      (hconst:((Dmax:ℝ)+2*(3*d:ℕ))≤ρ*Fintype.card V/2)
      (event:OrdinaryTriangleSeparatedCoverEvent P F π d Dmax B a p γ ρhub pR pH ηrow θ ρ j raw)
      (hωparent:0<ωparent) (hpReserve:0<p) (hηrow:0≤ηrow) (hεTri:0≤εTri)
      (hpR0:0≤pR) (hpR1:pR≤1) (hpHlower:p≤pH) (hpHupper:pH≤1)
      (hBsize:ωparent*Fintype.card V≤((Finset.univ\B).card:ℝ))
      (Dmean:ℝ) (hreg:∀v,|(P.degree v:ℝ)-Dmean|≤εTri*Fintype.card V)
      (hidentity:pR*Dmean=2*Fintype.card U*pH) (hbalance:εTri+2*b≤2*ωparent*p*ηrow),
    OrdinaryCleanupParentProfiles P Q F H π d I B pR pH density (εR*I.card) (εH*B.card) Ledit βe βh s j raw→
    OrdinaryNonrootNumericInputs F I T B W n₀ d ω b b b a ζlimit ε δcut ζcut εcut pH εR εH Ledit href→
    0<pH→pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→0≤Ledit→
    δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    OrdinaryInducedRimCutEvent I (sampledOrientation (rawWheelGraph P raw) coins) αcut pstar→
    (∀v,F.degree v≤2*(3*d))→
    (∀v:I,|(((Q.induce (I:Set V)).degree v):ℝ)-2*(Finset.univ.filter (fun u:B=>H v.val u.val)).card|≤η*I.card)→
    0<a→a≤1→80*ξ≤a^2→Fintype.card U≤Fintype.card V→Q≤P→
    (∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u∈W,(3)∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∃(D:SimpleGraph V) (J:V→U→Prop),
      D≤spanningRestriction Q I ∧ (∀v∈T,∀w∈T,¬D.Adj v w) ∧
      (∀v u,J v u→(H v u∧v∈I∧u∈B)∧¬(v∈T∧u∈W)) ∧
      (∀v,((spanningRestriction Q I)\D).degree v=
        2*(Finset.univ.filter (fun u=>(H v u∧v∈I∧u∈B)∧¬J v u)).card) ∧
      (∀u,(3)∣(Finset.univ.filter (fun v=>(H v u∧v∈I∧u∈B)∧¬J v u)).card) ∧
      (∀x:V⊕U,((ordinaryPhysicalGraph D J).degree x:ℝ)≤10*ξ*I.card) ∧
      let ReservedRim:=ordinaryRimRootStar ((spanningRestriction Q I)\D) T;
      let ReservedSpokes:=ordinarySpokeRootStar (fun v u=>(H v u∧v∈I∧u∈B)∧¬J v u) T W;
      let Qout:=Q\ReservedRim;
      let Hout:=fun v u=>H v u∧¬ReservedSpokes v u;
      let E:=(ordinaryHostResources D J).filter (ordinaryResourceTouchesRoots T W);
      ∃M:Finset (OrdinaryWheel Qout F Hout (3)),
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
  obtain ⟨η₀,hη₀,n₀,hmain⟩:=ordinary_sample_profile_triangle_separated_both_cuts ω ε δcut ξ hω hε hδ hδsmall hξ hξε
  refine ⟨η₀,hη₀,n₀,?_⟩
  intro η hη hη0 V U Γ Color _ _ _ _ _ _ Q P F H I T B W π d j raw coins
    a b p γ ζlimit pR pH density εR εH Ledit βe βh ζcut εcut href αcut pstar ηrow θ ρ ρhub εTri ωparent Dmax s
    ha hb hγ hLV hLU hIscale hJscale hbudget hcap hθscale hconst event hωparent hpReserve hηrow hεTri
    hpR0 hpR1 hpHlower hpHupper hBsize Dmean hreg hidentity hbalance profile hnums
    hpH hpH1 hεcut hζcut hζlimit hLedit hδlim hhref hRim hFcut hbal haPos ha1 hξsmall hU hQ hQbal hHdiv
  rcases hnums with ⟨hTI,hWB,hn,hIpos,hBpos,hωI,hBI,hTsize,hWsize,hδp,hζp,hhp,hhrim,
    herror,hcol,hrow,hcutbudget,hI,hT,hW,hL,hLsmall,hF,hedit,hbudgetI,hbudgetB,hnlarge⟩
  have hNparent:0<Fintype.card V:=lt_of_lt_of_le hIpos (Finset.card_le_univ I)
  have hBcard:(B.card:ℝ)≤b*Fintype.card V:=by
    have hh:(B.card:ℝ)≤I.card:=by exact_mod_cast hBI
    exact hh.trans hI
  have hUlower:ωparent*Fintype.card V≤Fintype.card U:=by
    have hh:((Finset.univ\B).card:ℝ)≤Fintype.card U:=by exact_mod_cast Finset.card_le_univ (Finset.univ\B)
    exact hBsize.trans hh
  have hmat:=ordinary_induced_rim_cut_smaller_parameter I (sampledOrientation (rawWheelGraph P raw) coins)
    αcut pstar δcut href hRim hδlim hhref
  exact hmain η hη hη0 V U Γ Color Q P F H I T B W hTI hWB hn hωI hBI hTsize hWsize π d j raw coins
    a b p γ (b*(Fintype.card V:ℝ)/2) (ζlimit*I.card) pR pH density (εR*I.card) (εH*B.card) 0 Ledit βe βh εcut ζcut ζlimit href ηrow θ ρ ρhub εTri ωparent (2*(3*d)) Dmax s
    ha hb hγ hLV hLU hIscale hJscale hbudget hcap hθscale hconst hBcard event hNparent hωparent hpReserve hηrow hεTri
    hpR0 hpR1 hpHlower hpHupper hBsize hUlower Dmean hreg hidentity hbalance profile hIpos hBpos hpH hpH1 hεcut hζcut hδp hζp hhp hζlimit hedit hhrim hmat hFcut herror hcol hrow hcutbudget
    hLedit hbal hedit haPos ha1 hξsmall hU hnlarge hI hT hW hL hLsmall hF hQ hbudgetI hbudgetB hQbal hHdiv
end Oberwolfach
