module

public import Oberwolfach.OrdinaryShiftedApproximateLoadsShared

@[expose] public section
/-! Name the ordinary approximate wheel-load event on the expanded first
sample. The shifted closing arc reads the ordinary physical state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryShiftedMixedLoadEvent
    {V U Γ Color IM IO:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype IM] [Fintype IO]
    [LinearOrder V] [DecidableEq U] (P:SimpleGraph V) (π:Equiv.Perm V) (d mM:ℕ) (mO:IO→ℕ)
    (p₂ k₂:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (H₀ Hₖ:V→U→Prop)
    (wM:∀i:IM,MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd mM π (3*d) H₀ Hₖ→ℝ)
    (gM:IM→Γ) (jM:IM→Color)
    (wO:∀i:IO,OrderedOrdinaryWheel (U:=U) π (3*d) (mO i+1)→ℝ)
    (gO:IO→Γ) (jO:IO→Color) (tM:ℝ) (tO:IO→ℝ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):Prop :=
      (∀i root,|typedMarkedPotentialLoad (wM i) (ordinaryShiftedPairRims P π d (fun e=>rawExpandedApproximateCollapse e (σ e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (σ e)) (gM i) (jM i)) root-
        ∑W,(if root∈typedMarkedOccurrenceResources W then wM i W else 0)*
          ∏a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ p₂ q s (gM i) (jM i) a|<tM) ∧
      (∀i root,|resourcePatternLoad orderedOrdinaryResources (wO i) (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d (gO i) (jO i) (fun e=>rawExpandedApproximateCollapse e (σ e)))-
        ∑W,(if root∈orderedOrdinaryResources W then wO i W else 0)*
          ∏a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (gO i) (jO i) (orderedOrdinaryResourceEmbedding a)|<tO i)
end Oberwolfach
