module

public import Oberwolfach.OrdinaryTriangleFinitePackingNonrootDegree
public import Oberwolfach.OrdinaryTriangleScaledBudgets

@[expose] public section
/-! Discharge the triangle finite-packing balance and edit bounds using the
regular parent host and a single asymptotically small parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_uniform_finite_packing_with_nonroot_degree
    (P F Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d Dmax:ℕ)
    (κ p γ ω η θ ρ ρhub L pR pH D ε:ℝ)
    (hκ:0<κ) (hp:0<p) (hγ:0<γ) (hω:0<ω) (hη:0≤η)
    (hscale:48*κ≤p^6*γ*min 1 ω) (hρhub:13*κ≤ρhub) (hρ:54*κ≤ρ)
    (hθ:κ≤θ) (hbalance:3*κ≤2*ω*p*η) (hε:0≤ε) (hεsmall:ε≤κ)
    (hpR:0≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hn:0<Fintype.card V) (hreg:∀v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V)
    (hidentity:pR*D=2*Fintype.card U*pH)
    (hL:0≤L) (hLsmall:L≤κ*Fintype.card V)
    (hconst:((Dmax:ℝ)+2*(3*d:ℕ))≤ρ*Fintype.card V/2)
    (j:Color) (sample:RawWheelOutcome V U Γ Color)
    (I:Finset V) (J:Finset U) (hI:(I.card:ℝ)≤κ*Fintype.card V)
    (hJ:(J.card:ℝ)≤κ*Fintype.card V)
    (hB:ω*Fintype.card V≤((Finset.univ\J).card:ℝ))
    (hPre:OrdinaryPrescribedInnerEvent 3 P F π d κ p γ Finset.univ Finset.univ j sample)
    (hHub:OrdinaryHubCoverEvent 2 P F π d ρhub j sample)
    (hTri:OrdinaryTriangleTwoDomainRowEvent P F π d Dmax Finset.univ Finset.univ
      (Finset.univ\J) pR pH η θ ρ j sample)
    (hQ:Q≤P\F) (hFL:∀v,(F.degree v:ℝ)≤L)
    (hQR:∀v,((changed ((rawWheelGraph P sample).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hHr:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d sample j v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hHc:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d sample j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)
    (E:Finset (Sym2 V⊕(V×U))) (D₀:ℕ)
    (hE:E⊆ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J))
    (hFE:∀v w,Sum.inl s(v,w)∈E→¬F.Adj v w)
    (hDE:∀t,(E.filter (ordinaryResourceIncident t)).card≤D₀)
    (hEcard:(E.card:ℝ)≤κ^2*(Fintype.card V:ℝ)^2) (hD₀:(D₀:ℝ)≤κ*Fintype.card V)
    (T:Finset V) (W:Finset U) (hTI:T⊆I) (hWJ:W⊆J)
    (hTcard:(T.card:ℝ)≤κ*Fintype.card V) (hWcard:(2*W.card:ℝ)≤L)
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
        18*κ*Fintype.card V+3*((W.card:ℝ)+T.card)) ∧
      (∀u∉W,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inr u):ℝ)≤
        9*κ*Fintype.card V+3*(T.card:ℝ)):=by
  have hUlo:ω*Fintype.card V≤(Fintype.card U:ℝ):=hB.trans (Nat.cast_le.mpr (Finset.card_le_univ _))
  have hmiss:(Fintype.card U:ℝ)-(Finset.univ\J).card≤κ*Fintype.card V:=by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ J),Finset.card_univ,
      Nat.cast_sub (Finset.card_le_univ J)]
    linarith only [hJ]
  have hbalance':ε+2*κ≤2*ω*p*η:=by linarith only [hεsmall,hbalance]
  have hratio:=ordinary_triangle_parent_balance P (Finset.univ\J) pR pH D ε κ ω p η
    hn hω hp hη hε hκ.le hpR hpR1 hpH hpH1 hB hmiss hreg hidentity hbalance'
  have hs:=ordinary_triangle_scaled_budgets κ p γ ω η ρ ρhub θ (Fintype.card V) (Fintype.card U)
    L I.card J.card T.card ((Dmax:ℝ)+2*(3*d:ℕ))
    hκ.le hp.le hγ.le hω (Nat.cast_nonneg _) hscale hρhub hρ hθ hbalance hUlo hL hLsmall
    (Nat.cast_nonneg _) hI (Nat.cast_nonneg _) hJ (Nat.cast_nonneg _) hTcard hconst
  obtain ⟨hL',hLV,hLU,hI',hJ',hbudget,hLhub,hcap,hTcard',_⟩:=hs
  apply ordinary_triangle_finite_packing_with_nonroot_degree P F Q H π d Dmax κ p γ L (13*κ*Fintype.card V) pR pH η θ ρ ρhub
    hκ.le hL hL' hLV hLU hbudget hLhub j sample I J hI' hJ' hPre hHub hTri hQ hFL hQR hHr hHc
    E D₀ hE hFE hDE hEcard hD₀ T W hTI hWJ
    (by convert hcap using 1 <;> push_cast <;> ring_nf)
    hTcard' (hWcard.trans (by nlinarith only [hbudget,hκ]))
    (fun v _=>hratio v) hWdiv hTbal hErim hErow hEcol
end Oberwolfach
