module

public import Oberwolfach.OrdinaryConstructedCorrectionTriangleSeparatedCoverNonroot
public import Oberwolfach.OrdinaryCorrectedStarPackingAvoidance

@[expose] public section
/-! The same-sample correction and bounded wheel packing also preserve the
    deeper induced pair in the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_constructed_correction_triangle_separated_cover_protected_nonroot
    (ω h δ ξ:ℝ) (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4)
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
      (∀v:I,|(((Q.induce (I:Set V)).degree v):ℝ)-
        2*(Finset.univ.filter (fun u:B=>H v.val u.val)).card|≤η*I.card)→
    ∀(π:Equiv.Perm V) (d:ℕ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (a b p γ L Lbase pR pH ηrow θ ρ ρhub εTri ωparent:ℝ) (Dmax:ℕ)
    (ha:0≤a) (hb:0≤b) (hγ:0≤γ)
    (hLV:6*b≤p^6*γ/4) (hLU:6*b≤(p^6*γ/4)*ωparent)
    (hIscale:b≤p^6*γ/8) (hJscale:b≤(p^6*γ/8)*ωparent)
    (hbudget:b+12*a≤ρhub) (hcap:3*b+24*a≤ρ/2) (hθscale:b≤θ)
    (hconst:((Dmax:ℝ)+2*(3*d:ℕ))≤ρ*Fintype.card V/2)
    (hBcard:(B.card:ℝ)≤b*Fintype.card V)
    (event:OrdinaryTriangleSeparatedCoverEvent P F π d Dmax B a p γ ρhub pR pH ηrow θ ρ j raw)
    (hNparent:0<Fintype.card V) (hωparent:0<ωparent) (hp:0<p) (hηrow:0≤ηrow) (hεTri:0≤εTri)
    (hpR0:0≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hBsize:ωparent*Fintype.card V≤((Finset.univ\B).card:ℝ)) (hU:ωparent*Fintype.card V≤Fintype.card U)
    (Dmean:ℝ) (hreg:∀v,|(P.degree v:ℝ)-Dmean|≤εTri*Fintype.card V)
    (hidentity:pR*Dmean=2*Fintype.card U*pH) (hbalance:εTri+2*b≤2*ωparent*p*ηrow),
      (⌈10*ξ*I.card⌉₊:ℝ)≤a*Fintype.card V→
      ((Fintype.card (V⊕U)*⌈10*ξ*I.card⌉₊:ℕ):ℝ)≤a^2*(Fintype.card V:ℝ)^2→
      (I.card:ℝ)≤b*Fintype.card V→(T.card:ℝ)≤b*Fintype.card V→
      (2*W.card:ℝ)≤L→0≤L→L≤b*Fintype.card V→
      (∀v,(F.degree v:ℝ)≤L)→Q≤P\F→Lbase+I.card≤L→Lbase+B.card≤L→
      (∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤Lbase)→
      (∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v)) (Finset.univ.filter (H v))).card:ℝ)≤Lbase)→
      (∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u))
        (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤Lbase)→
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
  obtain ⟨η₀,hη₀,n₀,hmain⟩:=ordinary_constructed_correction_triangle_separated_cover_nonroot ω h δ ξ hω hh hδ hδsmall hξ hξh
  refine ⟨η₀,hη₀,n₀,?_⟩
  intro η hη hη0 V U Γ Color _ _ _ _ _ _ Q P F H I T B W hTI hWB hn hωI hBI hTsize hWsize
    R horient hcutR hcutH hbal π d j raw a b p γ L Lbase pR pH ηrow θ ρ ρhub εTri ωparent Dmax
    ha hb hγ hLV hLU hIscale hJscale hbudget hcap hθscale hconst hBcard event hNparent hωparent hp hηrow hεTri
    hpR0 hpR1 hpH hpH1 hBsize hU Dmean hreg hidentity hbalance hDscale hEscale hI hT hW hL hLsmall hF hQP
    hbudgetI hbudgetB hQR hHr hHc hQbal hHdiv
  obtain ⟨D,J,hDI,hDavoid,hJ,hCbal,hKdiv,hdegree,hM⟩:=hmain η hη hη0 V U Γ Color Q P F H I T B W
    hTI hWB hn hωI hBI hTsize hWsize R horient hcutR hcutH
    (by intro v;convert hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    π d j raw a b p γ L Lbase pR pH ηrow θ ρ ρhub εTri ωparent Dmax
    ha hb hγ hLV hLU hIscale hJscale hbudget hcap hθscale hconst hBcard event hNparent hωparent hp hηrow hεTri
    hpR0 hpR1 hpH hpH1 hBsize hU Dmean hreg hidentity hbalance hDscale hEscale hI hT hW hL hLsmall hF hQP hbudgetI hbudgetB hQR hHr hHc hQbal hHdiv
  refine ⟨D,J,hDI,hDavoid,hJ,?_,?_,hdegree,?_⟩
  · intro v;convert hCbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro u;convert hKdiv u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · dsimp only at hM ⊢
    obtain ⟨M,hpair,hinner,hr,hs,hc,hboundR,hboundH⟩:=hM
    refine ⟨M,hpair,hinner,hr,hs,hc,hboundR,hboundH,?_⟩
    exact ordinary_corrected_star_packing_avoids_deeper Q D F H J I T B W 3 hTI hWB hDavoid
      (fun v u h=>(hJ v u h).2) M
end Oberwolfach
