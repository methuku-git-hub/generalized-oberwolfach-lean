module

public import Oberwolfach.EndpointPhysicalPotentialProbability
public import Oberwolfach.EndpointPhysicalParentTypedBounds

@[expose] public section
/-! Choose the physical parent matchings before sampling and obtain both
root-omitted potential estimates on the same original-law sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_physical_parent_potential_event (K ω p₀ t:ℝ)
    (hK:1≤K) (hω:0<ω) (hp₀:0<p₀) (ht:0<t) (d q₀:ℕ) (hd:2≤d):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],∀(P:SimpleGraph V) (A X:Finset V),N≤A.card→
      (∀x∈X,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ))→
    ∃weight:V→Sym2 (V⊕U)→ℝ,EndpointPhysicalParentWeights P A X weight ∧
    ∀(F:SimpleGraph V) (π:Equiv.Perm V) (B:Finset U),
      (Fintype.card V:ℝ)≤K*A.card→(Fintype.card U:ℝ)≤K*A.card→ω*A.card≤(B.card:ℝ)→
      permutationConflictGraph π (3*d)≤F→(∀z l,0<l→l<2*d+1→(π^l) z≠z)→
    ∀(pR pH:ℝ) (hpR0:p₀≤pR) (hpR1:pR≤1) (hpH0:p₀≤pH)
      (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (j:Color),(∀u∈B,s u j=pH)→
    1-2/(A.card:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
        (EndpointPhysicalPotentialEvent P F A B X π d j weight pR pH t):=by
  obtain ⟨N,hN⟩:=endpoint_physical_potential_common_event K ω p₀ 40 t hK hω hp₀ (by norm_num) ht d q₀ hd
  refine ⟨max N 32,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P A X hn hdeg
  obtain ⟨weight,hweight⟩:=endpoint_physical_parent_weight_family (U:=U) P A X (by omega) hdeg
  refine ⟨weight,hweight,?_⟩
  intro F π B hV hU hB hF hshort pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj
  obtain ⟨hw,hz,he⟩:=endpoint_physical_parent_typed_bounds P F A X weight hweight
  exact hN V U Γ Color P F π A B X (by omega) hV hU hB hF hshort pR pH hpR0 hpR1 hpH0
    q hq hQ s hs hS j hj weight hw hz he
end Oberwolfach
