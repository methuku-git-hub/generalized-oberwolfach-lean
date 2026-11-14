module

public import Oberwolfach.FiniteProjectedProductEvent
public import Oberwolfach.ExpandedOrdinarySelectedLaw
public import Oberwolfach.FiniteSigmaFirstMap
public import Oberwolfach.OrdinaryRawHubParentPrior
public import Oberwolfach.OrdinaryReferenceAndInnerRimProbability

@[expose] public section
/-! Transfer the complete raw parent/reference/rim event to any earlier
    event of the same expanded state and the same physical direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_expanded_raw_parent_reference_rim_with_prior
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (d k:ℕ) (hd:2≤d)
    (p k₁ p₂ k₂ u pH:ℝ) (hp:0≤p) (hk₁:0≤k₁) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k₁+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (j:Color) (endpointWeight:V→Sym2 (V⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
    (α pstar βP ηP ηH βH c Bweight t tR tH δ h αinner:ℝ)
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
    (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (a b:ℝ) :
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k₁ p₂ k₂ u hp hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS);
    let ν:=FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.fairCoin);
    1-a≤((μ.sigma ρ).prod ν).probability E →
    1-b≤(μraw.prod ν).probability (fun z=>
      OrdinaryRawHubParentPrior d k P F A Z π j s endpointWeight triangleWeight
        α pstar βP ηP ηH βH c Bweight (2*p) pH t tR tH z.1 ∧
      OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2 ∧
      OrdinaryInducedRimCutEvent A (sampledOrientation (rawWheelGraph P z.1) z.2) αinner pstar) →
    1-a-b≤((μ.sigma ρ).prod ν).probability (fun z=>
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      E z ∧ OrdinaryRawHubParentPrior d k P F A Z π j s endpointWeight triangleWeight
        α pstar βP ηP ηH βH c Bweight (2*p) pH t tR tH raw ∧
      OrdinaryTriangleReferenceMatrixCuts P F π d j δ h raw z.2 ∧
      OrdinaryInducedRimCutEvent A (sampledOrientation (rawWheelGraph P raw) z.2) αinner pstar) := by
  intro μ μraw ν hE hRaw
  let f:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→RawWheelOutcome V U Γ Color:=
    fun σ e=>expandedOrdinarySelectedCollapse e (σ e)
  have hproj:(μ.sigma ρ).map (fun z=>f z.1)=μraw:=by
    calc
      _ = ((μ.sigma ρ).map Sigma.fst).map f:=by rw [finiteLaw_map_map]
      _ = μ.map f:=by rw [finiteLaw_sigma_map_first_dependent]
      _ = μraw:=expanded_ordinary_selected_wheel_law p k₁ p₂ k₂ u hp hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  let G:RawWheelOutcome V U Γ Color×(Sym2 V→Bool)→Prop:=fun z=>
    OrdinaryRawHubParentPrior d k P F A Z π j s endpointWeight triangleWeight
      α pstar βP ηP ηH βH c Bweight (2*p) pH t tR tH z.1 ∧
    OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2 ∧
    OrdinaryInducedRimCutEvent A (sampledOrientation (rawWheelGraph P z.1) z.2) αinner pstar
  exact finite_projected_product_event (μ.sigma ρ) μraw ν (fun z=>f z.1) hproj E G a b hE hRaw
end Oberwolfach
