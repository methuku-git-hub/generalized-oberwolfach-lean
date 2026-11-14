module

public import Oberwolfach.MarkedVortexInnerActiveSizeInputs
public import Oberwolfach.MarkedVortexInnerHubSizes
public import Oberwolfach.MarkedFixedVortexScaleInputs

@[expose] public section
/-! The actual vortex supplies the three neighbourhood size comparisons. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_neighbourhood_size_inputs
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρ₀:0<ρ₀)
    (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (hehalf:ε≤1/2) (hm:0<m)
    (K:ℝ) (hK:0≤K) (hKI:1≤K*(ε/2)) (hKJ:1≤K*(ρ₀/8)*(ε/2))
    (L:ℕ) (hL:L<Q.length):
    ∀i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let I:=markedVortexInnerVertices Q i
      let J:=markedVortexInnerHubs Q i
      (Fintype.card W:ℝ)≤K*I.card ∧ (Fintype.card Z:ℝ)≤K*I.card ∧
      (Fintype.card W:ℝ)≤K*J.card := by
  have hI:=marked_vortex_inner_active_size_inputs Q he hehalf hm (ε/2) (by positivity) le_rfl L hL
  have hJ:=marked_vortex_inner_hub_sizes Q hreg hn hD hρ₀ hρlo hρhi hb hb1 he hm (ρ₀/8) le_rfl L hL
  intro i hi W Z I J
  have hIlo: (ε/2)*(Fintype.card W:ℝ)≤I.card:=(hI i hi).1
  have hJlo: (ρ₀/8)*(I.card:ℝ)≤J.card:=(hJ i hi).1
  have hZW:Fintype.card Z≤Fintype.card W:=
    (marked_vortex_reference_scale_inputs Q hreg hn hD hρ₀ hρlo hρhi hb hb1 he hm i (by omega)).2.2.1
  have hW0:0≤(Fintype.card W:ℝ):=Nat.cast_nonneg _
  have hKIn:=mul_le_mul_of_nonneg_right hKI hW0
  have hIJ:=mul_le_mul_of_nonneg_left hIlo hK
  have hKn:=mul_le_mul_of_nonneg_right hKJ hW0
  have hIJ' :=mul_le_mul_of_nonneg_left hIlo (mul_nonneg hK (by positivity : 0≤ρ₀/8))
  have hJJ:=mul_le_mul_of_nonneg_left hJlo hK
  have hWI:(Fintype.card W:ℝ)≤K*I.card:=by nlinarith
  have hWJ:(Fintype.card W:ℝ)≤K*J.card:=by nlinarith
  exact ⟨hWI,(by exact_mod_cast hZW : (Fintype.card Z:ℝ)≤Fintype.card W) |>.trans hWI,hWJ⟩
end Oberwolfach
