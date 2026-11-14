module

public import Oberwolfach.EndpointFactorFromFixedWeights
public import Oberwolfach.EndpointParentMatching
public import Oberwolfach.EndpointSourceDomain

@[expose] public section

/-! The source endpoint factor with edge-domain matching weights and the
actual classes A and B in an arbitrary ambient vertex set. The zero extension
and absence of conflict edges at index vertices are derived here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_factor_from_parent_matching (p κ c C : ℝ)
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
      HasResourceDecomposition (endpointTriangleVertices
        (Q:=endpointHostGraph R H A B) (F:=F) (S:=S) (T:=T)) (S∪T) := by
  obtain ⟨ε₀,τ,η,K,hε,hτ,hη,hK,N,hfactor⟩:=endpoint_factor_from_fixed_weights p κ c C hp hp1 hκ hc hC
  refine ⟨ε₀,τ,η,K,hε,hτ,hη,hK,max N 1,?_⟩
  intro V _ _ P R H F A B x hn hAB hxB hR hFsupp q s ε L δ ξ
    hq hq1 hs hs1 hε' hL hδ hLτ hB hBA hdeg hF hrows hindices
    parentWeight hparent hparentSum
  dsimp only
  intro hbalance hrow hindex herr hratio
  have haN : 0<A.card := (le_max_right N 1).trans hn
  have ha : 0<(A.card:ℝ) := by exact_mod_cast haN
  obtain ⟨hw,hsum,hzero,hpos⟩:=endpoint_parent_matching_extension P F (A∩P.neighborFinset x) x
    A.card c C ha hc.le hC.le parentWeight hparent hparentSum
  apply hfactor V P R H F A B x ((le_max_left N 1).trans hn)
    hAB hR
    (endpoint_conflict_no_index F A B x hAB hxB hFsupp)
    q s ε L δ ξ hq hq1 hs hs1 hε' hL hδ hLτ hB hBA hdeg hF
    (by convert hrows using 1 <;> congr!) hindices
    (graphEdgeWeightExtension (spanningRestriction P (A∩P.neighborFinset x)) parentWeight)
    hw hsum hzero hpos hbalance (by convert hrow using 1 <;> congr!) hindex herr hratio

end Oberwolfach
