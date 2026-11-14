module

public import Oberwolfach.EndpointPhysicalPotentialEvent
public import Oberwolfach.OrdinaryTriangleFullExpandedJoint

@[expose] public section
/-! The fixed endpoint-potential event, an arbitrary earlier expanded event
(including matching data), and the reference cuts all use the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem endpoint_physical_event_with_expanded_prior
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (ν:FiniteLaw (Sym2 V→Bool))
    (E:(Σσ,R σ)→Prop) (a b c:ℝ) (P F:SimpleGraph V) (π:Equiv.Perm V) (j:Color) (δ h:ℝ)
    (A:Finset V) (B:Finset U) (X:Finset V) (weight:V→Sym2 (V⊕U)→ℝ) (pH t:ℝ)
    (hn:0<Fintype.card V) (hU:0<Fintype.card U):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS);
    1-a≤(μ.sigma ρ).probability E→
    1-b≤μraw.probability (EndpointPhysicalPotentialEvent P F A B X π d j weight (2*p) pH t)→
    1-c≤(μraw.prod ν).probability (fun z=>OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2)→
    1-a-b-c≤((μ.sigma ρ).prod ν).probability (fun z=>
      (E z.1 ∧ EndpointPhysicalPotentialEvent P F A B X π d j weight (2*p) pH t
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      OrdinaryTriangleReferenceNormalizedCuts P F π d j δ h
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) z.2):=by
  exact ordinary_triangle_raw_and_reference_with_expanded_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ρ ν E (EndpointPhysicalPotentialEvent P F A B X π d j weight (2*p) pH t) a b c P F π j δ h hn hU
end Oberwolfach
