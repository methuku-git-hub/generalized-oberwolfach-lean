module

public import Oberwolfach.EndpointAndDeepProfilesProbability
public import Oberwolfach.OrdinaryRawHubParentPrior

@[expose] public section
/-! The endpoint and deeper-profile parts of the raw parent prior are
    supplied by the original sampling law, with weights fixed beforehand. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_raw_hub_prior_with_deep_probability (K ω p₀ t ε : ℝ)
    (hK : 1≤K) (hω : 0<ω) (hp₀ : 0<p₀) (ht : 0<t) (hε : 0<ε)
    (d q₀ : ℕ) (hd : 2≤d) :
    ∃ N : ℕ, ∀ (V U Γ Color : Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U], ∀ (P : SimpleGraph V) (A : Finset V), N≤A.card →
      (∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) →
    ∃ weight : V→Sym2 (V⊕U)→ℝ, EndpointPhysicalParentWeights P A Aᶜ weight ∧
    ∀ (F : SimpleGraph V) (π : Equiv.Perm V) (B : Finset U),
      (Fintype.card V:ℝ)≤K*A.card → (Fintype.card U:ℝ)≤K*A.card → ω*A.card≤(B.card:ℝ) →
      permutationConflictGraph π (3*d)≤F → (∀z l,0<l→l<2*d+1→(π^l) z≠z) →
    ∀ (pR pH : ℝ) (hpR0 : p₀≤pR) (hpR1 : pR≤1) (hpH0 : p₀≤pH)
      (q : U→Γ→ℝ) (hq : ∀u g,0≤q u g) (hQ : ∀u,∑g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀u j,0≤s u j)
      (hS : ∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (j : Color), (∀u,s u j=pH) →
    ∀ (k : ℕ) (triangleWeight : OrdinaryCycle P 3→ℝ)
      (α pstar βP ηP ηH βH c Bweight a : ℝ),
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hp₀.le.trans hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)
    1-a≤μ.probability (ordinaryCombinedTriangleEvent d k P F π (max (1/2) (cycleThreshold 3))
      α pstar βP ηP ηH βH c Bweight pR pH triangleWeight j) →
    1-a-3/(A.card:ℝ)^q₀≤μ.probability (OrdinaryRawHubParentPrior d k P F A B π j s weight triangleWeight
      α pstar βP ηP ηH βH c Bweight pR pH t (ε*A.card) (ε*B.card)) := by
  obtain ⟨N,hN⟩:=endpoint_and_deep_profiles_common_probability K ω p₀ t ε hK hω hp₀ ht hε d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P A hA hdeg
  have hdeg' : ∀x∈Aᶜ,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ) := by
    intro x hx v hv
    exact hdeg x (Finset.mem_compl.mp hx) v hv
  obtain ⟨weight,hw,hweight⟩:=hN V U Γ Color P A Aᶜ hA hdeg'
  refine ⟨weight,hw,?_⟩
  intro F π B hV hU hB hF hshort pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj
    k triangleWeight α pstar βP ηP ηH βH c Bweight a μ htri
  let E : RawWheelOutcome V U Γ Color → Prop := ordinaryCombinedTriangleEvent d k P F π (max (1/2) (cycleThreshold 3))
    α pstar βP ηP ηH βH c Bweight pR pH triangleWeight j
  let D : RawWheelOutcome V U Γ Color → Prop := fun σ=>EndpointPhysicalPotentialEvent P F A B Aᶜ π d j weight pR pH t σ ∧
    RawOrdinaryRows P π d 3 A pR s j (ε*A.card) σ ∧
    RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card) σ
  have hD:1-3/(A.card:ℝ)^q₀≤μ.probability D:=hweight F π B hV hU hB hF hshort
    pR pH hpR0 hpR1 hpH0 q hq hQ s hs hS j hj
  have hboth:1-a-3/(A.card:ℝ)^q₀≤μ.probability (fun σ=>E σ∧D σ):=
    (sub_le_sub_right htri _).trans (finiteLaw_good_intersection μ E D _ hD)
  exact hboth
end Oberwolfach
