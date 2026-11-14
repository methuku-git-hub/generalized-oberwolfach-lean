module

public import Oberwolfach.EndpointPhysicalParentPotentialEvent
public import Oberwolfach.OrdinaryDeepDomainNeighbourhoodEvent

@[expose] public section
/-! The fixed endpoint parent weights and deeper row/column estimates hold
    together on the original ambient sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_and_deep_profiles_common_probability (K ω p₀ t ε : ℝ)
    (hK : 1≤K) (hω : 0<ω) (hp₀ : 0<p₀) (ht : 0<t) (hε : 0<ε)
    (d q₀ : ℕ) (hd : 2≤d) :
    ∃ N : ℕ, ∀ (V U Γ Color : Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U], ∀ (P : SimpleGraph V) (A X : Finset V), N≤A.card →
      (∀x∈X,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
    ∃ weight : V→Sym2 (V⊕U)→ℝ, EndpointPhysicalParentWeights P A X weight ∧
    ∀ (F : SimpleGraph V) (π : Equiv.Perm V) (B : Finset U),
      (Fintype.card V:ℝ)≤K*A.card → (Fintype.card U:ℝ)≤K*A.card → ω*A.card≤(B.card:ℝ) →
      permutationConflictGraph π (3*d)≤F → (∀z l,0<l→l<2*d+1→(π^l) z≠z) →
    ∀ (pR pH : ℝ) (hpR0 : p₀≤pR) (hpR1 : pR≤1) (hpH0 : p₀≤pH)
      (q : U→Γ→ℝ) (hq : ∀u g,0≤q u g) (hQ : ∀u,∑g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀u j,0≤s u j)
      (hS : ∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (j : Color), (∀u,s u j=pH) →
    1-3/(A.card:ℝ)^q₀≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
        (fun σ=>EndpointPhysicalPotentialEvent P F A B X π d j weight pR pH t σ ∧
          RawOrdinaryRows P π d 3 A pR s j (ε*A.card) σ ∧
          RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card) σ) := by
  obtain ⟨N₁,hN₁⟩:=endpoint_physical_parent_potential_event K ω p₀ t hK hω hp₀ ht d q₀ hd
  obtain ⟨N₂,hN₂⟩:=ordinary_three_domain_neighbourhood_common_event K ω ε hK hω hε d q₀ hd
  refine ⟨max N₁ N₂,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P A X hA hdeg
  obtain ⟨weight,hw,hwprob⟩:=hN₁ V U Γ Color P A X (le_trans (le_max_left _ _) hA) hdeg
  refine ⟨weight,hw,?_⟩
  intro F π B hV hU hB hF hshort pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj
  let μ:=FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)
  let E : RawWheelOutcome V U Γ Color → Prop := EndpointPhysicalPotentialEvent P F A B X π d j weight pR pH t
  let D : RawWheelOutcome V U Γ Color → Prop := fun σ=>RawOrdinaryRows P π d 3 A pR s j (ε*A.card) σ ∧
    RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card) σ
  have hE:1-2/(A.card:ℝ)^q₀≤μ.probability E:=hwprob F π B hV hU hB hF hshort
    pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j (fun u _=>hj u)
  have hD:1-1/(A.card:ℝ)^q₀≤μ.probability D:=hN₂ V U Γ Color P F π A B
    (le_trans (le_max_right _ _) hA) hV hU hB hF hshort pR (hp₀.le.trans hpR0) hpR1 q hq hQ s hs hS j pH hj
  have hboth:1-2/(A.card:ℝ)^q₀-1/(A.card:ℝ)^q₀≤μ.probability (fun σ=>E σ∧D σ):=
    (sub_le_sub_right hE _).trans (finiteLaw_good_intersection μ E D _ hD)
  convert hboth using 1 <;> ring
end Oberwolfach
