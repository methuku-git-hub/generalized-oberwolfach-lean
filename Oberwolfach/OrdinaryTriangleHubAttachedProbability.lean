module

public import Oberwolfach.OrdinaryTriangleHubAfterSpacing

@[expose] public section
/-! Name the triangle fine-cover, row, cut and hub-weight probability bound
with its arbitrary product-sample prior. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleHubAttachedProbability
    (n qCount D mv d:ℕ) (β ε α κ aLoad p pH pmin εR εH δcap b Bweight ηHub:ℝ)
    (P:SimpleGraph (Fin n)) (Q:Vortex (Fin qCount) P D β ε mv) (π:Equiv.Perm (Fin n))
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (density tR tH βe βh:ℕ→ℝ) (s:Fin qCount→Bool→ℝ) (j:Bool)
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)]
    (μ:FiniteLaw (∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e))
    (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
    (loss χdeep χHub χone χtwo χcut:ℝ):Prop :=
    let κcoins:=FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin)
    let αcut:=min (α/4) (1/4:ℝ)
    let Prior:=OrdinaryTriangleFineRowsCutsEvent d κ aLoad εR εH αcut pmin p pH P D mv β ε Q π hπ s j E;
    1-(loss+χdeep+χone+χtwo+χcut+χHub)≤((μ.sigma ν).prod κcoins).probability (fun z=>
      Prior z ∧ OrdinaryVortexAdaptiveHubAllLevelsEvent 2 d D mv β ε p pH δcap b Bweight ηHub
        density tR tH βe βh P Q π hπ s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))
end Oberwolfach
