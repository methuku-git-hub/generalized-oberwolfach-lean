module

public import Oberwolfach.MarkedVortexCorrectionLevelFacts
public import Oberwolfach.MarkedVortexInnerBalanceScale

@[expose] public section
/-! Keep the correction and all level facts while deriving the inner-scale
balance estimate on each used later level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_vortex_correction_adds_inner_scale_balance
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ) (εAbs ζ:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m) (L:ℕ)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (he:0<ε) (hm:0<m) (hL:L<Q.length)
    (η εBal ζBal:ℝ) (hη:0≤η) (hsmall:εBal+((r+4)+2:ℕ)*ζBal≤η*ε/2)
    (C:∀i,RawMarkedOutcome (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color →
      (Bool→markedVortexVertexType Q i→markedVortexHubType Q i→Prop)→Prop)
    (hprojection: ∀ i, 1 ≤ i → i ≤ L → ∀ σi Hi, C i σi Hi →
      MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexPermutation Q π hpres i) d (r+4)
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i)
        ((εBal+((r+4)+2:ℕ)*ζBal)*Fintype.card (markedVortexVertexType Q i)) σi Hi)
    (hcor:MarkedVortexAbsorbableCorrectionWithLevelFacts P π d r size a₀ b₀ e₀ f₀ εAbs ζ σ H D m β ε Q L C):
    let F:=fun i σi Hi=>C i σi Hi ∧
      MarkedLevelFiniteBalanceBound (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexPermutation Q π hpres i) d (r+4)
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i)
        (η*(markedVortexInnerVertices Q i).card) σi Hi;
    MarkedVortexAbsorbableCorrectionWithLevelFacts P π d r size a₀ b₀ e₀ f₀ εAbs ζ σ H D m β ε Q L F := by
  intro F
  obtain ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs,hbalance,hrestr,hfacts⟩:=hcor
  refine ⟨DA,DS,hsub,havoid,hrim,hspoke,hdiv,habs,hbalance,hrestr,?_⟩
  intro i hi hli
  have hc:=hfacts i hi hli
  refine ⟨hc,?_⟩
  exact marked_vortex_inner_balance_from_ambient P π D m β ε Q hpres he hm r d η εBal ζBal hη hsmall i
    (lt_of_le_of_lt hli hL) _ _ (hprojection i hi hli _ _ hc)
end Oberwolfach
