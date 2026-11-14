module

public import Oberwolfach.EndpointFixedWeightEstimates
public import Oberwolfach.EndpointSourceFactor

@[expose] public section

/-! The endpoint-factor conclusion with the supplied parent fractional
matching. Triangle coefficients are constructed here from the unchanged
matching, rather than assumed to satisfy the factor theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_factor_from_fixed_weights (p κ c C : ℝ)
    (hp : 0<p) (hp1 : p≤1) (hκ : 0<κ) (hc : 0<c) (hC : 0<C) :
    ∃ ε₀ τ η K : ℝ,0<ε₀ ∧ 0<τ ∧ 0<η ∧ 0<K ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V],
      ∀ (P R H F : SimpleGraph V) (A B : Finset V) (x : V),N≤A.card →
      Disjoint A B → R≤P\F →
      (∀ u∈B,∀ w,¬F.Adj u w) →
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
      ∀ weight : Sym2 V→ℝ,
      (∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
        0≤weight s(v,w) ∧ weight s(v,w)≤C/A.card) →
      (∀ v∈A∩P.neighborFinset x,∑ w∈A∩P.neighborFinset x,weight s(v,w)=1) →
      (∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
        ¬P.Adj v w → weight s(v,w)=0) →
      (∀ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
        c/A.card≤weight e ∧ weight e≤C/A.card) →
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
      HasResourceDecomposition (endpointTriangleVertices
        (Q:=endpointHostGraph R H A B) (F:=F) (S:=S) (T:=T)) (S∪T) := by
  obtain ⟨ε₀,τ,η,hε,hτ,hη,N,hfactor⟩:=endpoint_source_factor p κ c (C/(κ*p^5))
    hp hp1 hκ hc (by positivity)
  let K:=2*C+(1+2*C)/(2*κ*p)
  have hK : 0<K := by dsimp [K];positivity
  refine ⟨ε₀,τ,η,K,hε,hτ,hη,hK,max N 1,?_⟩
  intro V _ _ P R H F A B x hn hAB hR hFB q s ε L δ ξ
    hq hq1 hs hs1 hε' hL hδ hLτ hB hBA hdeg hF hrows hindices
    weight hw hsum hzero hpos hbalance hrow hindex herr
  dsimp only
  intro hratio
  have ha : 0<(A.card:ℝ) := by exact_mod_cast (le_max_right N 1).trans hn
  have hwts:=endpoint_fixed_weight_estimates P R H F A B x hAB hR hFB κ p q s c C L δ ξ
    ha hκ hp hc.le hC.le hL hδ hB hBA hq hq1 hs hs1 hF weight hw hsum hzero hpos hbalance
    (by convert hrow using 1 <;> congr!) hindex
  apply hfactor V P R H F A B x ((le_max_left N 1).trans hn) hBA hAB hR q s ε L
    hq hs hε' hL hLτ hB hdeg hF
    (by convert hrows using 1 <;> congr!) hindices hratio
    (fun D=>weight (endpointTriangleRowEdge D)/(B.card*q^2*s^3)) hwts.1
  intro v hv
  exact (hwts.2 v hv).trans herr

end Oberwolfach
