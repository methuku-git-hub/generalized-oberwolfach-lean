module

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

theorem ordinary_triangle_separated_cover_from_joint
    (P F Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d D:ℕ)
    (a p γ L L' pR pH η θ ρ ρhub εTri jfrac ω:ℝ) (ha:0≤a) (hL:0≤L) (hL':0≤L')
    (hLV:6*L≤(p^6*γ/4)*Fintype.card V) (hLU:6*L≤(p^6*γ/4)*Fintype.card U)
    (hbudget:L+12*a*Fintype.card V≤L') (hLhub:L'≤ρhub*Fintype.card V)
    (j:Color) (sample:RawWheelOutcome V U Γ Color)
    (I:Finset V) (J:Finset U) (hI:(I.card:ℝ)≤p^6*γ*Fintype.card V/8)
    (hJ:(J.card:ℝ)≤p^6*γ*Fintype.card U/8)
    (hJoint:OrdinaryTriangleSeparatedCoverEvent P F π d D J a p γ ρhub pR pH η θ ρ j sample)
    (hn:0<Fintype.card V) (hω:0<ω) (hp:0<p) (hη:0≤η) (hεTri:0≤εTri) (hjfrac:0≤jfrac)
    (hpR0:0≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hB:ω*Fintype.card V≤((Finset.univ\J).card:ℝ)) (hJfrac:(J.card:ℝ)≤jfrac*Fintype.card V)
    (Dmean:ℝ) (hreg:∀v,|(P.degree v:ℝ)-Dmean|≤εTri*Fintype.card V)
    (hidentity:pR*Dmean=2*Fintype.card U*pH) (hbalanceScale:εTri+2*jfrac≤2*ω*p*η)
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
    (hcap:2*L'+T.card+D+2*(3*d:ℕ)≤ρ*Fintype.card V)
    (hTcard:(T.card:ℝ)≤θ*Fintype.card V) (hWcard:(2*W.card:ℝ)≤L')
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
  have hmiss:(Fintype.card U:ℝ)-(Finset.univ\J).card≤jfrac*Fintype.card V:=by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ J),Finset.card_univ,
      Nat.cast_sub (Finset.card_le_univ J)]
    linarith only [hJfrac]
  have hbalance:=ordinary_triangle_parent_balance P (Finset.univ\J) pR pH Dmean εTri jfrac ω p η
    hn hω hp hη hεTri hjfrac hpR0 hpR1 hpH hpH1 hB hmiss hreg hidentity hbalanceScale
  exact ordinary_triangle_finite_packing_with_nonroot_degree P F Q H π d D a p γ L L' pR pH η θ ρ ρhub
    ha hL hL' hLV hLU hbudget hLhub j sample I J hI hJ hJoint.1 hJoint.2.1 hJoint.2.2
    hQ hFL hQR hHr hHc E D₀ hE hFE hDE hEcard hD₀ T W hTI hWJ hcap hTcard hWcard
    (fun v _=>hbalance v) hWdiv hTbal hErim hErow hEcol
end Oberwolfach
