module

public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! The true parent has no more hubs than vertices. Consequently its size,
multiplied by the vortex scale, is linearly bounded by either inner domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_normalized_parent_bounds
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    {P:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U P D β ε m)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ₀:0<ρ₀)
    (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<m) (i:ℕ) (hi:i<Q.length):
    ε*(Fintype.card (markedVortexVertexType Q i)+Fintype.card (markedVortexHubType Q i):ℝ)≤
      4*(markedVortexInnerVertices Q i).card ∧
    (ρ₀/8)*ε*(Fintype.card (markedVortexVertexType Q i)+Fintype.card (markedVortexHubType Q i):ℝ)≤
      4*(markedVortexInnerHubs Q i).card :=by
  obtain ⟨hI,hB,hUP⟩:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε hm i hi
  have hUP':(Fintype.card (markedVortexHubType Q i):ℝ)≤Fintype.card (markedVortexVertexType Q i):=by exact_mod_cast hUP
  have hE:=mul_le_mul_of_nonneg_left hUP' hε.le
  have hParent:ε*(Fintype.card (markedVortexVertexType Q i)+Fintype.card (markedVortexHubType Q i):ℝ)≤
      4*(markedVortexInnerVertices Q i).card:=by nlinarith only [hI,hE]
  have hscaled:=mul_le_mul_of_nonneg_left hParent (show 0≤ρ₀/8 by positivity)
  constructor
  · exact hParent
  · nlinarith only [hscaled,hB]
end Oberwolfach
