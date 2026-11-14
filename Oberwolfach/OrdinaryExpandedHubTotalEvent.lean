module

public import Oberwolfach.ExpandedOrdinaryHubTotalFamily

@[expose] public section
/-! Named full ordinary-wheel weight tests for each hub and each length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryExpandedHubTotalEvent
    {V U Γ Color I:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I]
    [LinearOrder V] [DecidableEq U] (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (m:I→ℕ)
    (p₂ k₂:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (w:∀i,OrderedOrdinaryWheel (U:=U) π (3*d) (m i+1)→ℝ)
    (g:I→Γ) (j:I→Color) (η:I→ℝ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):Prop :=
∀i hub,
      |orderedOrdinarySampledHubTotal P π d (m i) (w i) (g i) (j i) hub (fun e=>rawExpandedApproximateCollapse e (σ e))-
       ∑W,orderedOrdinaryHubWeight (w i) hub W *
        ∏a∈orderedOrdinaryResources W,rawMarkedWheelMarginal P π d p₂ k₂ q s (g i) (j i) (orderedOrdinaryResourceEmbedding a)|<η i*Fintype.card V
end Oberwolfach
