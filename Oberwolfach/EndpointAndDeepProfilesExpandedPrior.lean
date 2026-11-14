module

public import Oberwolfach.EndpointPhysicalEventExpandedPrior
public import Oberwolfach.TriangleDomainNeighbourhoodEvent

@[expose] public section
/-! Join the deeper three-root common profiles, the physical endpoint
potentials, any earlier expanded event and the reference cuts on one sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem endpoint_and_deep_profiles_with_expanded_prior
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (ν:FiniteLaw (Sym2 V→Bool))
    (E:(Σσ,R σ)→Prop) (a b c e:ℝ) (P F:SimpleGraph V) (π:Equiv.Perm V) (j:Color) (δ h:ℝ)
    (A:Finset V) (B:Finset U) (X:Finset V) (weight:V→Sym2 (V⊕U)→ℝ) (pH t ε:ℝ)
    (hn:0<Fintype.card V) (hU:0<Fintype.card U):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS);
    1-a≤(μ.sigma ρ).probability E→
    1-b≤μraw.probability (EndpointPhysicalPotentialEvent P F A B X π d j weight (2*p) pH t)→
    1-e≤μraw.probability (fun σ=>RawOrdinaryRows P π d 3 A (2*p) s j (ε*A.card) σ ∧
      RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card) σ)→
    1-c≤(μraw.prod ν).probability (fun z=>OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2)→
    1-a-b-e-c≤((μ.sigma ρ).prod ν).probability (fun z=>
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      (E z.1 ∧ EndpointPhysicalPotentialEvent P F A B X π d j weight (2*p) pH t raw ∧
        (RawOrdinaryRows P π d 3 A (2*p) s j (ε*A.card) raw ∧
          RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card) raw)) ∧
      OrdinaryTriangleReferenceNormalizedCuts P F π d j δ h raw z.2):=by
  intro μ μraw hE hpot hcounts hcuts
  have hboth:1-(b+e)≤μraw.probability (fun σ=>
      EndpointPhysicalPotentialEvent P F A B X π d j weight (2*p) pH t σ ∧
      (RawOrdinaryRows P π d 3 A (2*p) s j (ε*A.card) σ ∧
        RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card) σ)):=by
    have hh:1-b-e≤μraw.probability _:=
      (sub_le_sub_right hpot e).trans (finiteLaw_good_intersection μraw _ _ e hcounts)
    linarith
  have hh:=ordinary_triangle_raw_and_reference_with_expanded_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ρ ν E (fun σ=>EndpointPhysicalPotentialEvent P F A B X π d j weight (2*p) pH t σ ∧
      (RawOrdinaryRows P π d 3 A (2*p) s j (ε*A.card) σ ∧
        RawOrdinaryDomainIndices F π d 3 B pH j (ε*B.card) σ))
    a (b+e) c P F π j δ h hn hU hE hboth hcuts
  convert hh using 1 <;> try ring
end Oberwolfach
