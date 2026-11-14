module

public import Oberwolfach.EndpointParentWeightFamily
public import Oberwolfach.EndpointPotentialEstimates
public import Oberwolfach.TriangleDomainNeighbourhoodEvent

@[expose] public section

/-! The actual parent weights and one simultaneous triangle count/potential
event. The weights precede the density arrays, and the threshold is uniform
in those arrays. Root neighbourhoods are counted in the original domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triangle_sampling_with_parent_weights (K ω p₀ ε t:ℝ)
    (hK:1≤K) (hω:0<ω) (hp₀:0<p₀) (hε:0<ε) (ht:0<t) (d q₀:ℕ) (hd:2≤d):
    ∃ N:ℕ,∀ (V Γ Color:Type) [Fintype V] [Fintype Γ] [Fintype Color] [DecidableEq V],
    ∀ (P:SimpleGraph V) (A X:Finset V),N≤A.card →
      (Fintype.card V:ℝ)≤K*A.card →
      (∀ x∈X,∀ v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
    ∃ weight:V→Sym2 V→ℝ,
      (∀ x∈X,
        (∀ v∈A∩P.neighborFinset x,∀ w∈A∩P.neighborFinset x,
          0≤weight x s(v,w)∧weight x s(v,w)≤40/A.card) ∧
        (∀ v∈A∩P.neighborFinset x,∑ w∈A∩P.neighborFinset x,weight x s(v,w)=1) ∧
        (∀ v w,¬P.Adj v w→weight x s(v,w)=0) ∧
        (∀ F:SimpleGraph V,∀ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
          (1/30:ℝ)/A.card≤weight x e∧weight x e≤40/A.card)) ∧
      ∀ (F:SimpleGraph V) (π:Equiv.Perm V) (B:Finset V),ω*A.card≤(B.card:ℝ) →
      (∀ x∈X,Disjoint (insert x A) B) → permutationConflictGraph π (3*d)≤F →
      (∀ z l,0<l→l<2*d+1→(π^l) z≠z) →
      ∀ (pR pH:ℝ) (hpR0:p₀≤pR) (hpR1:pR≤1) (hpH0:p₀≤pH)
        (q:V→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
        (s:V→Color→ℝ) (hs:∀ u j,0≤s u j)
        (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
        (j:Color),(∀ u,s u j=pH) →
      1-1/(A.card:ℝ)^q₀≤
        (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
          (fun σ=>(RawOrdinaryRows P π d 3 A pR s j (ε*A.card) σ ∧
              RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card) σ) ∧
            EndpointPotentialEstimates P F π d A B X pR pH j weight t σ):=by
  obtain ⟨N₁,h₁⟩:=triangle_domain_neighbourhood_common_event K ω ε hK hω hε d (q₀+1) hd
  obtain ⟨N₂,h₂⟩:=endpoint_potential_common_event K ω p₀ 40 t hK hω hp₀ (by norm_num) ht d (q₀+1) hd
  refine ⟨max 32 (max N₁ N₂),?_⟩
  intro V Γ Color _ _ _ _ P A X hn hV hdeg
  obtain ⟨weight,hw⟩:=endpoint_parent_weight_family P A X (by omega) hdeg
  refine ⟨weight,hw,?_⟩
  intro F π B hB hAB hF hnoshort pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj
  have hcounts:=h₁ V V Γ Color P F π A B (by omega) hV hV hB hF hnoshort
    pR (hp₀.le.trans hpR0) hpR1 q hq hQ s hs hS j pH hj
  have hpot:=h₂ V Γ Color P F π A B X (by omega) hV hB hAB hF hnoshort
    pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j (fun u _=>hj u) weight
    (fun x hx=>(hw x hx).1) (fun x hx v _ w _=>(hw x hx).2.2.1 v w)
  have hnum:=scaled_inverse_power_le A.card q₀ (by omega) 2 (by exact_mod_cast (show 2≤A.card by omega))
  apply le_trans _ (finiteLaw_good_intersection _ _ _ (1/(A.card:ℝ)^(q₀+1)) hpot)
  calc
    _≤(1-1/(A.card:ℝ)^(q₀+1))-1/(A.card:ℝ)^(q₀+1):=by
      have hh:2*(1/(A.card:ℝ)^(q₀+1))≤1/(A.card:ℝ)^q₀:=by convert hnum using 1 <;> ring
      linarith only [hh]
    _≤_:=sub_le_sub_right (by convert hcounts using 1 <;> congr!) _

end Oberwolfach
