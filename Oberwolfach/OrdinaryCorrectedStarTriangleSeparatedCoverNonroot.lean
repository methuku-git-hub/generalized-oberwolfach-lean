module

public import Oberwolfach.OrdinaryCorrectionStarCoverInputs
public import Oberwolfach.OrdinaryTriangleTwoScaleCoverFromJoint

@[expose] public section
/-! The finite same-sample triangle cover event covers the correction star
    and then all protected roots, with the corrected inner star reserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_corrected_star_triangle_separated_cover_nonroot
    (P F Q D:SimpleGraph V) (H J:V→U→Prop) (I T:Finset V) (B W:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (a b p γ L pR pH η θ ρ ρhub εTri ω:ℝ) (Dmax D₀:ℕ)
    (ha:0≤a) (hb:0≤b) (hγ:0≤γ)
    (hLV:6*b≤p^6*γ/4) (hLU:6*b≤(p^6*γ/4)*ω)
    (hIscale:b≤p^6*γ/8) (hJscale:b≤(p^6*γ/8)*ω)
    (hbudget:b+12*a≤ρhub) (hcap:3*b+24*a≤ρ/2) (hθscale:b≤θ)
    (hconst:((Dmax:ℝ)+2*(3*d:ℕ))≤ρ*Fintype.card V/2)
    (hBcard:(B.card:ℝ)≤b*Fintype.card V)
    (event:OrdinaryTriangleSeparatedCoverEvent P F π d Dmax B a p γ ρhub pR pH η θ ρ j raw)
    (hn:0<Fintype.card V) (hω:0<ω) (hp:0<p) (hη:0≤η) (hεTri:0≤εTri)
    (hpR0:0≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hBsize:ω*Fintype.card V≤((Finset.univ\B).card:ℝ)) (hU:ω*Fintype.card V≤Fintype.card U)
    (Dmean:ℝ) (hreg:∀v,|(P.degree v:ℝ)-Dmean|≤εTri*Fintype.card V)
    (hidentity:pR*Dmean=2*Fintype.card U*pH) (hbalance:εTri+2*b≤2*ω*p*η)
    (hTI:T⊆I) (hWB:W⊆B) (hDI:D≤spanningRestriction Q I)
    (hJ:∀v u,J v u→H v u∧v∈I∧u∈B)
    (hdegree:∀x:V⊕U,(ordinaryPhysicalGraph D J).degree x≤D₀)
    (hDscale:(D₀:ℝ)≤a*Fintype.card V)
    (hEscale:((Fintype.card (V⊕U)*D₀:ℕ):ℝ)≤a^2*(Fintype.card V:ℝ)^2)
    (hI:(I.card:ℝ)≤b*Fintype.card V) (hT:(T.card:ℝ)≤b*Fintype.card V)
    (hW:(2*W.card:ℝ)≤L) (hL:0≤L) (hLsmall:L≤b*Fintype.card V)
    (hF:∀v,(F.degree v:ℝ)≤L)
    (hQbal:∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hHdiv:∀u∈W,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (hCbal:∀v∈T,((spanningRestriction Q I)\D).degree v=
      2*(Finset.univ.filter (fun u=>(H v u∧v∈I∧u∈B)∧¬J v u)).card)
    (hKdiv:∀u∈W,3∣(Finset.univ.filter (fun v=>(H v u∧v∈I∧u∈B)∧¬J v u)).card):
    let R:=ordinaryRimRootStar ((spanningRestriction Q I)\D) T;
    let S:=ordinarySpokeRootStar (fun v u=>(H v u∧v∈I∧u∈B)∧¬J v u) T W;
    let Qout:=Q\R;
    let Hout:=fun v u=>H v u∧¬S v u;
    let E:=(ordinaryHostResources D J).filter (ordinaryResourceTouchesRoots T W);
    Qout≤P\F→
    (∀v,((changed ((rawWheelGraph P raw).neighborFinset v) (Qout.neighborFinset v)).card:ℝ)≤L)→
    (∀v,((changed (Finset.univ.filter (rawWheelSpokes π d raw j v)) (Finset.univ.filter (Hout v))).card:ℝ)≤L)→
    (∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d raw j v u))
      (Finset.univ.filter (fun v=>Hout v u))).card:ℝ)≤L)→
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
        9*a*Fintype.card V+3*(T.card:ℝ)):=by
  intro R S Qout Hout E hQP hQR hHr hHc
  have hC:((spanningRestriction Q I)\D)≤Q:=sdiff_le.trans (by
    intro v w h;exact (spanningRestriction_adj Q I v w).mp h |>.1)
  have hK:∀v u,((H v u∧v∈I∧u∈B)∧¬J v u)→H v u:=by intro v u h;exact h.1.1
  have hCb:∀v∈T,((spanningRestriction Q I)\D).degree v=
      2*(Finset.univ.filter (fun u=>(H v u∧v∈I∧u∈B)∧¬J v u)).card:=by
    intro v hv
    convert hCbal v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hrootbalance:=ordinary_corrected_inner_star_root_balance Q ((spanningRestriction Q I)\D) H
    (fun v u=>(H v u∧v∈I∧u∈B)∧¬J v u) T W 3 hC hK hQbal
    (by intro v hv;convert hCbal v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    hHdiv (by intro u hu;convert hKdiv u hu using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  change R≤Q ∧ (∀v u,S v u→H v u) ∧
    (∀v∈T,Qout.degree v=2*(Finset.univ.filter (Hout v)).card) ∧
    (∀u∈W,3∣(Finset.univ.filter (fun v=>Hout v u)).card) at hrootbalance
  have he:=ordinary_correction_star_cover_inputs Q D H J I T B W D₀ hTI hWB hDI hJ hdegree
  change E⊆ordinaryHostResources (spanningRestriction Qout I) (fun v u=>Hout v u∧v∈I∧u∈B) ∧
    (∀v∈T,∀w∈I,Qout.Adj v w→Sum.inl s(v,w)∈E) ∧
    (∀v∈T,∀u∈B,Hout v u→Sum.inr (v,u)∈E) ∧
    (∀u∈W,∀v∈I,Hout v u→Sum.inr (v,u)∈E) ∧
    (∀x,(E.filter (ordinaryResourceIncident x)).card≤D₀) ∧
    E.card≤Fintype.card (V⊕U)*D₀ at he
  have hEcard:(E.card:ℝ)≤a^2*(Fintype.card V:ℝ)^2:=
    (Nat.cast_le.mpr he.2.2.2.2.2).trans hEscale
  have hFE:∀v w,Sum.inl s(v,w)∈E→¬F.Adj v w:=by
    intro v w hvw hf
    have hq:Qout.Adj v w:=((spanningRestriction_adj Qout I v w).mp
      ((ordinaryHostResources_rim _ _ _).mp (he.1 hvw))).1
    exact (hQP hq).2 hf
  exact ordinary_triangle_two_scale_cover_from_joint P F Qout Hout π d Dmax
    a b p γ L pR pH η θ ρ ρhub εTri ω ha hb hγ hL hLsmall hLV hLU hIscale hJscale
    hbudget hcap hθscale hconst j raw I B hI hBcard event hn hω hp hη hεTri
    hpR0 hpR1 hpH hpH1 hBsize hU Dmean hreg hidentity hbalance hQP hF
    (by intro v;convert hQR v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hHr v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hHc u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) E D₀ he.1 hFE he.2.2.2.2.1 hEcard hDscale
    T W hTI hWB hT hW
    (by intro u hu;convert hrootbalance.2.2.2 u hu using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv;convert hrootbalance.2.2.1 v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) he.2.1 he.2.2.1 he.2.2.2.1
end Oberwolfach
