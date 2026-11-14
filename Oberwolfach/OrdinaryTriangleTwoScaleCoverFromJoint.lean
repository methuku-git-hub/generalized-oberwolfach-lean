module

public import Oberwolfach.OrdinaryTriangleSeparatedCoverFromJoint
public import Oberwolfach.OrdinaryTriangleSeparatedCoverEvent
public import Oberwolfach.OrdinaryTriangleFinitePackingNonrootDegree
public import Oberwolfach.OrdinaryTriangleParentBalance
public import Oberwolfach.OrdinaryTrianglePrescribedAssemblyNonroot
public import Oberwolfach.OrdinaryTrianglePrescribedUnionBounds
public import Oberwolfach.PrescribedEdgeEnumeration

@[expose] public section
/-! Replace indexed prescribed edges and roots by the actual finite sets,
while retaining the same-sample event and all numerical hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_two_scale_cover_from_joint
    (P F Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d D:ℕ)
    (a b p γ L pR pH η θ ρ ρhub εTri ω:ℝ)
    (ha:0≤a) (hb:0≤b) (hγ:0≤γ) (hL:0≤L)
    (hLsmall:L≤b*Fintype.card V)
    (hLVscale:6*b≤p^6*γ/4) (hLUscale:6*b≤(p^6*γ/4)*ω)
    (hIscale:b≤p^6*γ/8) (hJscale:b≤(p^6*γ/8)*ω)
    (hbudgetScale:b+12*a≤ρhub) (hcapScale:3*b+24*a≤ρ/2) (hθscale:b≤θ)
    (hconst:((D:ℝ)+2*(3*d:ℕ))≤ρ*Fintype.card V/2)
    (j:Color) (sample:RawWheelOutcome V U Γ Color)
    (I:Finset V) (J:Finset U) (hI:(I.card:ℝ)≤b*Fintype.card V)
    (hJ:(J.card:ℝ)≤b*Fintype.card V)
    (hJoint:OrdinaryTriangleSeparatedCoverEvent P F π d D J a p γ ρhub pR pH η θ ρ j sample)
    (hn:0<Fintype.card V) (hω:0<ω) (hp:0<p) (hη:0≤η) (hεTri:0≤εTri)
    (hpR0:0≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hB:ω*Fintype.card V≤((Finset.univ\J).card:ℝ)) (hU:ω*Fintype.card V≤Fintype.card U)
    (Dmean:ℝ) (hreg:∀v,|(P.degree v:ℝ)-Dmean|≤εTri*Fintype.card V)
    (hidentity:pR*Dmean=2*Fintype.card U*pH) (hbalanceScale:εTri+2*b≤2*ω*p*η)
    (hQ:Q≤P\F) (hFL:∀v,(F.degree v:ℝ)≤L)
    (hQR:∀v,((changed ((rawWheelGraph P sample).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hHr:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d sample j v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hHc:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d sample j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)
    (E:Finset (Sym2 V⊕(V×U))) (D₀:ℕ)
    (hE:E⊆ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J))
    (hFE:∀v w,Sum.inl s(v,w)∈E→¬F.Adj v w)
    (hDE:∀t,(E.filter (ordinaryResourceIncident t)).card≤D₀)
    (hEcard:(E.card:ℝ)≤a^2*(Fintype.card V:ℝ)^2) (hD₀:(D₀:ℝ)≤a*Fintype.card V)
    (T:Finset V) (W:Finset U) (hTI:T⊆I) (hWJ:W⊆J)
    (hTcard:(T.card:ℝ)≤b*Fintype.card V) (hWcard:(2*W.card:ℝ)≤L)
    (hWdiv:∀u∈W,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (hTbal:∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hErim:∀v∈T,∀w∈I,Q.Adj v w→Sum.inl s(v,w)∈E)
    (hErow:∀v∈T,∀u∈J,H v u→Sum.inr (v,u)∈E)
    (hEcol:∀u∈W,∀v∈I,H v u→Sum.inr (v,u)∈E):
    ∃ R:Finset (OrdinaryWheel Q F H 3),
      (∀A∈R,∀B∈R,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
      R.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
        (fun v u=>H v u∧v∈I∧u∈J)=E ∧
      (∀v∈T,∀w,(ordinaryWheelRimGraph R).Adj v w↔Q.Adj v w) ∧
      (∀v∈T,∀u,ordinaryPackingSpokes R v u↔H v u) ∧
      (∀u∈W,∀v,ordinaryPackingSpokes R v u↔H v u) ∧
      (∀v∉T,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inl v):ℝ)≤
        18*a*Fintype.card V+3*((W.card:ℝ)+T.card)) ∧
      (∀u∉W,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inr u):ℝ)≤
        9*a*Fintype.card V+3*(T.card:ℝ)):=by
  let N:ℝ:=Fintype.card V
  let Usize:ℝ:=Fintype.card U
  let L':ℝ:=(b+12*a)*N
  have hN:0≤N:=by positivity
  have hpγ:0≤p^6*γ/4:=by positivity
  have hL'0:0≤L':=by dsimp [L'];positivity
  have hLV:6*L≤(p^6*γ/4)*N:=by
    have hh:=mul_le_mul_of_nonneg_right hLVscale hN
    nlinarith only [hLsmall,hh]
  have hLU:6*L≤(p^6*γ/4)*Usize:=by
    have hh:=mul_le_mul_of_nonneg_right hLUscale hN
    have hh':=mul_le_mul_of_nonneg_left hU hpγ
    nlinarith only [hLsmall,hh,hh']
  have hI':(I.card:ℝ)≤p^6*γ*N/8:=by
    have hh:=mul_le_mul_of_nonneg_right hIscale hN
    nlinarith only [hI,hh]
  have hJ':(J.card:ℝ)≤p^6*γ*Usize/8:=by
    have hh:=mul_le_mul_of_nonneg_right hJscale hN
    have hh':=mul_le_mul_of_nonneg_left hU (show 0≤p^6*γ/8 by positivity)
    nlinarith only [hJ,hh,hh']
  have hbudget:L+12*a*N≤L':=by dsimp [L'];nlinarith only [hLsmall]
  have hLhub:L'≤ρhub*N:=by
    dsimp [L']
    exact mul_le_mul_of_nonneg_right hbudgetScale hN
  have hcap:2*L'+T.card+D+2*(3*d:ℕ)≤ρ*N:=by
    have hh:=mul_le_mul_of_nonneg_right hcapScale hN
    dsimp [L']
    push_cast at *
    nlinarith only [hTcard,hconst,hh]
  have hT':(T.card:ℝ)≤θ*N:=hTcard.trans (mul_le_mul_of_nonneg_right hθscale hN)
  have hW':(2*W.card:ℝ)≤L':=by nlinarith [hbudget,mul_nonneg ha hN]
  exact ordinary_triangle_separated_cover_from_joint P F Q H π d D a p γ L L' pR pH η θ ρ ρhub εTri b ω
    ha hL hL'0 hLV hLU hbudget hLhub j sample I J hI' hJ' hJoint hn hω hp hη hεTri hb
    hpR0 hpR1 hpH hpH1 hB hJ Dmean hreg hidentity hbalanceScale hQ hFL hQR hHr hHc
    E D₀ hE hFE hDE hEcard hD₀ T W hTI hWJ hcap hT' hW' hWdiv hTbal hErim hErow hEcol
end Oberwolfach
