module

public import Oberwolfach.OrdinaryTriangleReferencePriorProjection
public import Oberwolfach.ExpandedOrdinarySelectedLaw
public import Oberwolfach.FiniteSigmaFirstMap

@[expose] public section
/-! Attach the original ordinary reference cuts to any prior event in the
expanded marked/ordinary experiment, preserving its dependent sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_triangle_reference_with_expanded_prior
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (ν:FiniteLaw (Sym2 V→Bool))
    (E:(Σσ,R σ)→Prop) (a b:ℝ) (P F:SimpleGraph V) (π:Equiv.Perm V) (j:Color) (δ h:ℝ)
    (hn:0<Fintype.card V) (hU:0<Fintype.card U):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS);
    1-a≤(μ.sigma ρ).probability E→
    1-b≤(μraw.prod ν).probability (fun z=>OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2)→
    1-a-b≤((μ.sigma ρ).prod ν).probability (fun z=>E z.1 ∧
      OrdinaryTriangleReferenceNormalizedCuts P F π d j δ h
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) z.2):=by
  intro μ μraw hE hC
  let f:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→RawWheelOutcome V U Γ Color:=
    fun σ e=>expandedOrdinarySelectedCollapse e (σ e)
  have hproj:(μ.sigma ρ).map (fun z=>f z.1)=μraw:=by
    calc
      _ = ((μ.sigma ρ).map Sigma.fst).map f:=by rw [finiteLaw_map_map]
      _ = μ.map f:=by rw [finiteLaw_sigma_map_first_dependent]
      _ = μraw:=expanded_ordinary_selected_wheel_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  exact ordinary_triangle_reference_with_projected_prior (μ.sigma ρ) μraw ν (fun z=>f z.1) hproj
    E a b P F π d j δ h hn hU hE hC
end Oberwolfach
