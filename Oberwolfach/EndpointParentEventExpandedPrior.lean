module

public import Oberwolfach.EndpointPhysicalParentPotentialEvent
public import Oberwolfach.EndpointPhysicalEventExpandedPrior

@[expose] public section
/-! Parent matchings are chosen before sampling; their two physical
potentials, the reference cuts, and an arbitrary earlier expanded event
(such as a matching event) hold on the same expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_parent_event_with_expanded_prior (K ω p₀ t:ℝ)
    (hK:1≤K) (hω:0<ω) (hp₀:0<p₀) (ht:0<t) (d q₀:ℕ) (hd:2≤d):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],∀(P:SimpleGraph V) (A X:Finset V),N≤A.card→
      (∀x∈X,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ))→
    ∃weight:V→Sym2 (V⊕U)→ℝ,EndpointPhysicalParentWeights P A X weight ∧
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (F:SimpleGraph V) (π:Equiv.Perm V) (B:Finset U) (j:Color) (pH:ℝ),
      (Fintype.card V:ℝ)≤K*A.card→(Fintype.card U:ℝ)≤K*A.card→ω*A.card≤(B.card:ℝ)→
      permutationConflictGraph π (3*d)≤F→(∀z l,0<l→l<2*d+1→(π^l) z≠z)→
      p₀≤2*p→p₀≤pH→(∀u∈B,s u j=pH)→
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (ν:FiniteLaw (Sym2 V→Bool))
      (E:(Σσ,R σ)→Prop) (a c δ h:ℝ) (hn:0<Fintype.card V) (hU:0<Fintype.card U),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS);
    1-a≤(μ.sigma ρ).probability E→
    1-c≤(μraw.prod ν).probability (fun z=>OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2)→
    1-a-2/(A.card:ℝ)^q₀-c≤((μ.sigma ρ).prod ν).probability (fun z=>
      (E z.1 ∧ EndpointPhysicalPotentialEvent P F A B X π d j weight (2*p) pH t
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      OrdinaryTriangleReferenceNormalizedCuts P F π d j δ h
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) z.2):=by
  obtain ⟨N,hN⟩:=endpoint_physical_parent_potential_event K ω p₀ t hK hω hp₀ ht d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P A X hn hdeg
  obtain ⟨weight,hweight,hprob⟩:=hN V U Γ Color P A X hn hdeg
  refine ⟨weight,hweight,?_⟩
  intro p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS F π B j pH hV hU hB hF hshort hpR hpH hj
    R _ ρ ν E a c δ h hVpos hUpos μ μraw hE hC
  have hpR1:2*p≤1:=by linarith
  have hpot:=hprob F π B hV hU hB hF hshort (2*p) pH hpR hpR1 hpH q hq hQ s hs hS j hj
  exact endpoint_physical_event_with_expanded_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ρ ν E a (2/(A.card:ℝ)^q₀) c P F π j δ h A B X weight pH t hVpos hUpos hE hpot hC
end Oberwolfach
