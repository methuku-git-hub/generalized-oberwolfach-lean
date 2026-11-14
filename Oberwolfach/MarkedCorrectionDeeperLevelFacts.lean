module

public import Oberwolfach.MarkedVortexCorrectionLevelFacts
public import Oberwolfach.MarkedLevelFiniteBalanceBound
public import Oberwolfach.MarkedActualVortexBalanceProperty

@[expose] public section
/-! The deeper-domain event transfers to the same corrected sample at each
later vortex level, together with all previously established level facts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_correction_preserves_deeper_level_facts
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ:ℝ)
    (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m) (L LDeep:ℕ)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hLL:L≤LDeep) (epsBal ζBal:ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hDeep:MarkedActualVortexBalanceProperty Q π hpres d (r+4) LDeep a j epsBal ζBal
      (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z)
    (C:∀i,RawMarkedOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color →
      (Bool→markedVortexVertexType Q i→markedVortexHubType Q i→Prop)→Prop)
    (hcor:
      let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
      MarkedVortexAbsorbableCorrectionWithLevelFacts P π d r size a₀ b₀ e₀ f₀ εAbs ζ z.1 H D m β ε Q L C):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let B:=fun i σi Hi=>C i σi Hi ∧
      MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexPermutation Q π hpres i) d (r+4)
        (markedVortexDeeperVertices Q i) (markedVortexDeeperHubs Q i)
        ((epsBal+((r+4)+2:ℕ)*ζBal)*(markedVortexDeeperVertices Q i).card) σi Hi;
    MarkedVortexAbsorbableCorrectionWithLevelFacts P π d r size a₀ b₀ e₀ f₀ εAbs ζ z.1 H D m β ε Q L B := by
  intro H B
  obtain ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs,hbalance,hrestr,hfacts⟩:=hcor
  refine ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs,hbalance,hrestr,?_⟩
  intro i hi hli
  have hc:=hfacts i hi hli
  refine ⟨hc,?_⟩
  rw [(hrestr i hi).1,(hrestr i hi).2]
  dsimp only [MarkedActualVortexBalanceProperty] at hDeep
  exact (hDeep i (hli.trans hLL)).1
end Oberwolfach
