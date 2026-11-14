module

public import Oberwolfach.MarkedCorrectionDeeperThroughTerminal
public import Oberwolfach.MarkedCorrectionBothInitialScales

@[expose] public section
/-! Assemble the deeper estimates on the same corrected sample, including
all later levels and both initial domains at their own scales. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_correction_all_deeper_balances
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ:ℝ) (hζ:0≤ζ)
    (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m) (L:ℕ)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hterminal:L+1=Q.length) (he:0<ε) (hm:0<m)
    (η epsBal ζBal:ℝ) (hη:0≤η) (heps:0≤epsBal) (hζBal:0≤ζBal)
    (hbase:epsBal+((r+4)+2:ℕ)*ζBal≤η/2)
    (hcor:((r+4)+2:ℕ)*(4*ζ)≤η*ε^2/8)
    (a:Γ) (j:Color) (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hDeep:L=0 ∨ MarkedActualVortexBalanceProperty Q π hpres d (r+4) (L-1) a j epsBal ζBal
      (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z)
    (C:∀i,RawMarkedOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color →
      (Bool→markedVortexVertexType Q i→markedVortexHubType Q i→Prop)→Prop)
    (hstate:
      let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
      MarkedVortexCorrectionWithScaledFirstBalance P π d r size a₀ b₀ e₀ f₀ εAbs ζ z.1 H D m β ε Q L C η):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let B:=fun i σi Hi=>C i σi Hi ∧
      MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexPermutation Q π hpres i) d (r+4)
        (markedVortexDeeperVertices Q i) (markedVortexDeeperHubs Q i)
        ((epsBal+((r+4)+2:ℕ)*ζBal)*(markedVortexDeeperVertices Q i).card) σi Hi;
    MarkedVortexCorrectionWithBothScaledBalances P π d r size a₀ b₀ e₀ f₀ εAbs ζ z.1 H D m β ε Q L B η epsBal ζBal := by
  intro H B
  have hlevels:=marked_correction_deeper_facts_through_terminal P π d r size a₀ b₀ e₀ f₀ εAbs ζ D m β ε Q L hpres hterminal
    η epsBal ζBal heps hζBal a j z hDeep C hstate
  have hfirst:=marked_correction_first_deeper_balance_from_event P π d r size a₀ b₀ e₀ f₀ εAbs ζ hζ
    D m β ε Q L hpres hterminal η epsBal ζBal heps hζBal a j z hDeep B hlevels
  exact marked_correction_first_deeper_balance_at_inner_scale P π d r size a₀ b₀ e₀ f₀ εAbs ζ z.1 H
    D m β ε Q L he hm η epsBal ζBal hη hbase hcor B hfirst
end Oberwolfach
