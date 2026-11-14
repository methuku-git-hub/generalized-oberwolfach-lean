module

public import Oberwolfach.EndpointCompletedWheels
public import Oberwolfach.EndpointFactorFromParentMatching

@[expose] public section

/-! The physical triangle-root wheel conclusion from the original parent
matching, density profile and potential-load estimates. The endpoint
factor existence is supplied by its proved theorem, not a new premise. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_root_wheels_from_parent_matching (p κ c C : ℝ)
    (hp : 0<p) (hp1 : p≤1) (hκ : 0<κ) (hc : 0<c) (hC : 0<C) :
    ∃ ε₀ τ η K : ℝ,0<ε₀ ∧ 0<τ ∧ 0<η ∧ 0<K ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (P R H F : SimpleGraph V) (A B : Finset V) (x : V),N≤A.card →
      Disjoint A B → x∉B → R≤P\F →
      F.support⊆(insert x A:Set V) →
      ∀ q s ε L δ ξ : ℝ,p≤q → q≤1 → p≤s → s≤1 → ε≤ε₀ → 0≤L → 0≤δ →
      L≤τ*A.card → κ*A.card≤(B.card:ℝ) → B.card≤A.card →
      (∀ v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
      (∀ v,(F.degree v:ℝ)≤L) →
      (∀ X J : Finset V,x∈X → X⊆insert x A → J⊆B →
        X.card≤3 → J.card≤2 → X.card+J.card≤4 →
        q^X.card*s^J.card*((common A X (fun v=>(P\F).neighborFinset v)).card:ℝ)-ε*A.card≤
          ((common (common A X (fun v=>R.neighborFinset v)) J (fun v=>H.neighborFinset v)).card:ℝ)) →
      (∀ X : Finset V,x∈X → X⊆insert x A → (X.card=1 ∨ X.card=3) →
        (∀ v∈X,∀ w∈X,¬F.Adj v w) →
        (s^X.card-ε)*B.card≤((common B X (fun v=>H.neighborFinset v)).card:ℝ)) →
      ∀ parentWeight : (spanningRestriction P (A∩P.neighborFinset x)).edgeSet→ℝ,
      (∀ e,c/A.card≤parentWeight e ∧ parentWeight e≤C/A.card) →
      (∀ v∈A∩P.neighborFinset x,
        (∑ e:(spanningRestriction P (A∩P.neighborFinset x)).edgeSet,
          if v∈e.val then parentWeight e else 0)=1) →
      let weight:=graphEdgeWeightExtension (spanningRestriction P (A∩P.neighborFinset x)) parentWeight
      |q*(A∩P.neighborFinset x).card/(2*B.card*s)-1|≤δ →
      (∀ v∈common A {x} (fun y=>(P\F).neighborFinset y),
        |endpointRowPotential P R H F A B x v weight (B.card*q^2*s^3)-
          endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight s(v,w))|≤ξ) →
      (∀ u∈B,
        |endpointIndexPotential P R H F A x u weight (B.card*q^2*s^3)-
          q/(B.card*s)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight e)|≤ξ) →
      δ+K*L/A.card+ξ≤η →
      let S:=common A {x} (fun v=>R.neighborFinset v)
      let T:=common B {x} (fun v=>H.neighborFinset v)
      S.card=2*T.card →
      ∃ (M : Finset (EndpointTriangle (endpointHostGraph R H A B) F S T))
        (W : M→OrdinaryWheel R F H.Adj 3),
        (∀ C,ordinaryWheelHub (W C)=endpointTriangleIndex C.val ∧
          (ordinaryWheelRim (W C)).support.toFinset=insert x (C.val.val∩S)) ∧
        (∀ C D,C≠D → Disjoint (ordinaryWheelResources (W C)) (ordinaryWheelResources (W D))) ∧
        (∀ v∈S,∃! C,Sum.inl s(x,v)∈ordinaryWheelResources (W C)) ∧
        (∀ u∈T,∃! C,Sum.inr (x,u)∈ordinaryWheelResources (W C)) ∧
        (∀ v,v≠x → (wheelFamilyRim W).degree v≤2) ∧
        (∀ v,v≠x → (Finset.univ.filter (fun u=>wheelFamilySpokes W v u)).card≤1) ∧
        (∀ u,(Finset.univ.filter (fun v=>wheelFamilySpokes W v u)).card≤3) := by
  obtain ⟨ε₀,τ,η,K,hε,hτ,hη,hK,N,hfactor⟩:=endpoint_factor_from_parent_matching p κ c C hp hp1 hκ hc hC
  refine ⟨ε₀,τ,η,K,hε,hτ,hη,hK,N,?_⟩
  intro V _ _ P R H F A B x hn hAB hxB hR hFsupp q s ε L δ ξ
    hq hq1 hs hs1 hε' hL hδ hLτ hB hBA hdeg hF hrows hindices
    parentWeight hparent hparentSum
  dsimp only
  intro hbalance hrow hindex herr hratio
  have hfac:=hfactor V P R H F A B x hn hAB hxB hR hFsupp q s ε L δ ξ
    hq hq1 hs hs1 hε' hL hδ hLτ hB hBA hdeg hF hrows hindices
    parentWeight hparent hparentSum hbalance hrow hindex herr hratio
  apply endpoint_factor_completed_wheels R H F A B
    (common A {x} (fun v=>R.neighborFinset v)) (common B {x} (fun v=>H.neighborFinset v)) hAB
    (fun v hv=>((mem_common_iff _ _ _ _).mp hv).1)
    (fun v hv=>((mem_common_iff _ _ _ _).mp hv).1) x ?_ ?_ hfac
  · intro v hv
    have hrv : R.Adj x v:=(SimpleGraph.mem_neighborFinset R x v).mp
      (((mem_common_iff _ _ _ _).mp hv).2 x (Finset.mem_singleton_self _))
    exact ⟨hrv,(hR hrv).2⟩
  · intro u hu
    exact (SimpleGraph.mem_neighborFinset H x u).mp
      (((mem_common_iff _ _ _ _).mp hu).2 x (Finset.mem_singleton_self _))

end Oberwolfach
