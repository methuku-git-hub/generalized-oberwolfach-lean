module

public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! The fixed conflict-degree term is absorbed by the parent size once the
vortex's terminal-size parameter is chosen sufficiently large. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_fine_conflict_size_threshold
    (β ε ρ₀ ρ:ℝ) (d:ℕ) (hβ:0≤β) (hβ1:β≤1/4)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hρ:0<ρ):
    ∃m₀:ℕ,1≤m₀ ∧ ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→
      m₀≤m→∀Q:Vortex U P D β ε m,∀i,i<Q.length→
      3*(2*((3*d:ℕ):ℝ))≤ρ*Fintype.card (markedVortexVertexType Q i) :=by
  let C:ℝ:=3*(2*((3*d:ℕ):ℝ))
  obtain ⟨M,hM⟩:=exists_nat_gt (C/ρ)
  have hCM:C≤ρ*M:=by
    have hh:C<ρ*M:=by simpa only [mul_comm] using (div_lt_iff₀ hρ).mp hM
    linarith
  obtain ⟨m₀,hm₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q i hi
  have hs:=hsize V U P D m hreg hn hD hρlo hρhi hm Q i hi
  have hI:(M:ℝ)≤(markedVortexInnerVertices Q i).card:=by
    have hcard:0≤((markedVortexInnerVertices Q i).card:ℝ):=by positivity
    nlinarith only [hs.2.1,hε,hcard]
  have hparent:(M:ℝ)≤Fintype.card (markedVortexVertexType Q i):=
    hI.trans (by exact_mod_cast Finset.card_le_univ (markedVortexInnerVertices Q i))
  have hh:=mul_le_mul_of_nonneg_left hparent hρ.le
  dsimp [C] at hCM
  linarith only [hCM,hh]
end Oberwolfach
