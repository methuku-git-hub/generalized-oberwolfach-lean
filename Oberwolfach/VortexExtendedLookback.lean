module

public import Oberwolfach.VortexLookback
public import Oberwolfach.VortexExtended

@[expose] public section
/-! The strengthened paired estimates also hold for extended levels,
including the empty levels after termination. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem VortexLookback.extended_centre_estimates_lookback
    {V U:Type*} [Fintype V] [Fintype U] {G:SimpleGraph V}
    {D m t:ℕ} {β ε:ℝ} (Q:VortexLookback U G D β ε m t) (i:ℕ) (hi:0 < i):
    |2*((Q.toVortex.extendedIndices i).card:ℝ)/initialIndexDensity U D-
      ((D:ℝ)/Fintype.card V)*(Q.toVortex.extendedVertices i).card|≤β*(Q.toVortex.extendedVertices i).card ∧
    ∀x∈Q.toVortex.extendedVertices (i-(t+1)),
      |((G.neighborFinset x∩Q.toVortex.extendedVertices i).card:ℝ)-
        2*(Q.toVortex.extendedIndices i).card/initialIndexDensity U D|≤β*(Q.toVortex.extendedVertices i).card :=by
  by_cases hlen:i≤Q.length
  · rw [Q.toVortex.extendedVertices_eq hlen,Q.toVortex.extendedIndices_eq hlen,
      Q.toVortex.extendedVertices_eq (by omega:i-(t+1) ≤ Q.length)]
    exact Q.centre_estimates_lookback i hlen hi
  · rw [Q.toVortex.extendedVertices_empty (by omega:Q.length < i),
      Q.toVortex.extendedIndices_empty (by omega:Q.length < i)]
    simp
end Oberwolfach
