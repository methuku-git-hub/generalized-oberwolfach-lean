module

public import Oberwolfach.OrdinaryTriangleUniformPackingNonrootDegree

@[expose] public section
/-! The finite protected-edge and root-cover event for triangle wheels.
It is explicitly restricted to forbidden-edge-free hosts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

def OrdinaryTriangleFiniteCoverNonrootDegreeEvent (κ:ℝ) (P F:SimpleGraph V) (J:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color):Prop :=
  ∀ (Q:SimpleGraph V) (H:V→U→Prop) (L:ℝ),Q≤P\F → 0≤L → L≤κ*Fintype.card V →
    (∀v,(F.degree v:ℝ)≤L) →
    (∀v,((changed ((rawWheelGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
    (∀v,((changed (Finset.univ.filter (rawWheelSpokes π d σ j v)) (Finset.univ.filter (H v))).card:ℝ)≤L) →
    (∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L) →
    ∀I:Finset V,(I.card:ℝ)≤κ*Fintype.card V →
    ∀(E:Finset (Sym2 V⊕(V×U))) (D₀:ℕ),
      E⊆ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J) →
      (∀v w,Sum.inl s(v,w)∈E→¬F.Adj v w) →
      (∀t,(E.filter (ordinaryResourceIncident t)).card≤D₀) →
      (E.card:ℝ)≤κ^2*(Fintype.card V:ℝ)^2 → (D₀:ℝ)≤κ*Fintype.card V →
    ∀(T:Finset V) (W:Finset U),T⊆I → W⊆J →
      (T.card:ℝ)≤κ*Fintype.card V → (2*W.card:ℝ)≤L →
      (∀u∈W,3∣(Finset.univ.filter (fun v=>H v u)).card) →
      (∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card) →
      (∀v∈T,∀w∈I,Q.Adj v w→Sum.inl s(v,w)∈E) →
      (∀v∈T,∀u∈J,H v u→Sum.inr (v,u)∈E) →
      (∀u∈W,∀v∈I,H v u→Sum.inr (v,u)∈E) →
    ∃R:Finset (OrdinaryWheel Q F H 3),
      (∀A∈R,∀B∈R,A≠B→Disjoint (ordinaryWheelResources A) (ordinaryWheelResources B)) ∧
      R.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
        (fun v u=>H v u∧v∈I∧u∈J)=E ∧
      (∀v∈T,∀w,(ordinaryWheelRimGraph R).Adj v w↔Q.Adj v w) ∧
      (∀v∈T,∀u,ordinaryPackingSpokes R v u↔H v u) ∧
      (∀u∈W,∀v,ordinaryPackingSpokes R v u↔H v u) ∧
      (∀v∉T,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inl v):ℝ)≤
        18*κ*Fintype.card V+3*((W.card:ℝ)+T.card)) ∧
      (∀u∉W,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inr u):ℝ)≤
        9*κ*Fintype.card V+3*(T.card:ℝ))

theorem ordinary_triangle_joint_implies_finite_cover_nonroot_degree
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d Dmax:ℕ)
    (κ p γ ω η θ ρ ρhub pR pH D ε:ℝ)
    (hκ:0<κ) (hp:0<p) (hγ:0<γ) (hω:0<ω) (hη:0≤η)
    (hscale:48*κ≤p^6*γ*min 1 ω) (hρhub:13*κ≤ρhub) (hρ:54*κ≤ρ)
    (hθ:κ≤θ) (hbalance:3*κ≤2*ω*p*η) (hε:0≤ε) (hεsmall:ε≤κ)
    (hpR:0≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hn:0<Fintype.card V) (hreg:∀v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V)
    (hidentity:pR*D=2*Fintype.card U*pH)
    (hconst:((Dmax:ℝ)+2*(3*d:ℕ))≤ρ*Fintype.card V/2)
    (J:Finset U) (hJ:(J.card:ℝ)≤κ*Fintype.card V)
    (hB:ω*Fintype.card V≤((Finset.univ\J).card:ℝ))
    (j:Color) (sample:RawWheelOutcome V U Γ Color)
    (hPre:OrdinaryPrescribedInnerEvent 3 P F π d κ p γ Finset.univ Finset.univ j sample)
    (hHub:OrdinaryHubCoverEvent 2 P F π d ρhub j sample)
    (hTri:OrdinaryTriangleTwoDomainRowEvent P F π d Dmax Finset.univ Finset.univ
      (Finset.univ\J) pR pH η θ ρ j sample):
    OrdinaryTriangleFiniteCoverNonrootDegreeEvent κ P F J π d j sample:=by
  intro Q H L hQ hL hLsmall hFL hQR hHr hHc I hI E D₀ hE hFE hDE hEcard hD₀
    T W hTI hWJ hTcard hWcard hWdiv hTbal hErim hErow hEcol
  exact ordinary_triangle_uniform_finite_packing_with_nonroot_degree P F Q H π d Dmax κ p γ ω η θ ρ ρhub L pR pH D ε
    hκ hp hγ hω hη hscale hρhub hρ hθ hbalance hε hεsmall hpR hpR1 hpH hpH1
    hn hreg hidentity hL hLsmall hconst j sample I J hI hJ hB hPre hHub hTri hQ hFL hQR hHr hHc
    E D₀ hE hFE hDE hEcard hD₀ T W hTI hWJ hTcard hWcard hWdiv hTbal hErim hErow hEcol
end Oberwolfach
