module

public import Oberwolfach.EndpointRowPotentialEvent
public import Oberwolfach.EndpointIndexPotentialEvent
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! The two fixed-weight endpoint estimates hold on one raw event. The
uniform order threshold precedes all parent graphs, densities and weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- Both manuscript potential sums, with their unchanged eligible targets.
The finite sets A,B,X and the weights are fixed before the outcome. -/
def EndpointPotentialEstimates {V Γ Color:Type} [Fintype V] [Fintype Γ] [Fintype Color] [DecidableEq V]
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A B X:Finset V)
    (pR pH:ℝ) (j:Color) (weight:V→Sym2 V→ℝ) (t:ℝ) (σ:RawWheelOutcome V V Γ Color):Prop:=
  ∀ x∈X,∀ (hAB:Disjoint (insert x A) B),
    (∀ v∈common A {x} (fun z=>(P\F).neighborFinset z),
      |endpointRowPotential P (rawWheelGraph P σ)
        (bipartiteRelationGraph (insert x A) B hAB (rawWheelSpokes π d σ j)) F A B x v (weight x) (B.card*pR^2*pH^3)-
        endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight x s(v,w))|<t) ∧
    (∀ u∈B,|endpointIndexPotential P (rawWheelGraph P σ)
        (bipartiteRelationGraph (insert x A) B hAB (rawWheelSpokes π d σ j)) F A x u (weight x) (B.card*pR^2*pH^3)-
        pR/(B.card*pH)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight x e)|<t)

theorem endpoint_potential_common_event (K ω p₀ C t:ℝ)
    (hK:1≤K) (hω:0<ω) (hp₀:0<p₀) (hC:0<C) (ht:0<t) (d q₀:ℕ) (hd:2≤d):
    ∃ N:ℕ,∀ (V Γ Color:Type) [Fintype V] [Fintype Γ] [Fintype Color] [DecidableEq V],
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V) (A B X:Finset V),N≤A.card →
      (Fintype.card V:ℝ)≤K*A.card → ω*A.card≤(B.card:ℝ) →
      (∀ x∈X,Disjoint (insert x A) B) → permutationConflictGraph π (3*d)≤F →
      (∀ z l,0<l→l<2*d+1→(π^l) z≠z) →
    ∀ (pR pH:ℝ) (hpR0:p₀≤pR) (hpR1:pR≤1) (hpH0:p₀≤pH)
      (q:V→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:V→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u∈B,s u j=pH) →
    ∀ (weight:V→Sym2 V→ℝ),
      (∀ x∈X,∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
        0≤weight x s(v,w)∧weight x s(v,w)≤C/A.card) →
      (∀ x∈X,∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
        ¬P.Adj v w→weight x s(v,w)=0) →
    1-1/(A.card:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
        (EndpointPotentialEstimates P F π d A B X pR pH j weight t):=by
  obtain ⟨N₁,h₁⟩:=endpoint_row_potential_common_event K ω p₀ C t hK hω hp₀ hC ht d (q₀+1) hd
  obtain ⟨N₂,h₂⟩:=endpoint_index_potential_common_event K ω p₀ C t hK hω hp₀ hC ht d (q₀+1) hd
  refine ⟨max 2 (max N₁ N₂),?_⟩
  intro V Γ Color _ _ _ _ P F π A B X hn hV hB hAB hF hnoshort pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj weight hw hzero
  have hwedge (x:V) (hx:x∈X) (e:Sym2 V)
      (he:e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet):0≤weight x e∧weight x e≤C/A.card:=by
    induction e using Sym2.ind with
    | _ v w=>exact hw x hx v he.1 w he.2.1
  have hr:=h₁ V Γ Color P F π A B X (by omega) hV hB hAB hF hnoshort pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj weight hw hzero
  have hi:=h₂ V Γ Color P F π A B X (by omega) hV hB hAB hF hnoshort pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj weight hwedge
  have hnum:=scaled_inverse_power_le A.card q₀ (by omega) 2 (by exact_mod_cast (show 2≤A.card by omega))
  have hsum:1-1/(A.card:ℝ)^q₀≤(FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR)
      (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>(∀ x∈X,∀ (hAB:Disjoint (insert x A) B),∀ v∈common A {x} (fun z=>(P\F).neighborFinset z),
        |endpointRowPotential P (rawWheelGraph P σ) (bipartiteRelationGraph (insert x A) B hAB (rawWheelSpokes π d σ j)) F A B x v (weight x) (B.card*pR^2*pH^3)-
        endpointEligibleRowWeight F (A∩P.neighborFinset x) x v (fun v w=>weight x s(v,w))|<t) ∧
        (∀ x∈X,∀ (hAB:Disjoint (insert x A) B),∀ u∈B,
        |endpointIndexPotential P (rawWheelGraph P σ) (bipartiteRelationGraph (insert x A) B hAB (rawWheelSpokes π d σ j)) F A x u (weight x) (B.card*pR^2*pH^3)-
        pR/(B.card*pH)*(∑ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeFinset,weight x e)|<t)):=by
    apply le_trans _ (finiteLaw_good_intersection _ _ _ (1/(A.card:ℝ)^(q₀+1)) hi)
    calc
      _≤(1-1/(A.card:ℝ)^(q₀+1))-1/(A.card:ℝ)^(q₀+1):=by
        have hh:2*(1/(A.card:ℝ)^(q₀+1))≤1/(A.card:ℝ)^q₀:=by convert hnum using 1 <;> ring
        linarith only [hh]
      _≤_:=sub_le_sub_right (by convert hr using 1 <;> congr!) _
  apply hsum.trans
  apply finiteLaw_probability_mono
  intro σ hσ x hx hab
  exact ⟨hσ.1 x hx hab,hσ.2 x hx hab⟩

end Oberwolfach
