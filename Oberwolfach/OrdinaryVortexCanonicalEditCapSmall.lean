module

public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! A cap depending only on the fixed inner domains is small uniformly at
all levels when the fixed terminal size is sufficiently large. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_canonical_edit_cap_small
    (ε ρ₀ ζ δcap:ℝ) (d:ℕ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hζ:0<ζ) (hδcap:0≤δcap) (hδζ:δcap≤ζ/2):
    ∀β:ℝ,0≤β→β≤1/4→∃m₀:ℕ,1≤m₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (i:ℕ),i<Q.length→
    let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
    let L:=2*((3*d:ℕ):ℝ)+δcap*min (I.card:ℝ) B.card;
    0≤L ∧ L≤ζ*I.card := by
  intro β hβ hβ1
  obtain ⟨N,hN⟩:=exists_nat_gt ((2*((3*d:ℕ):ℝ))/(ζ/2))
  obtain ⟨m₀,hm₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ N
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q i hi I B L
  have hI0:(0:ℝ)≤I.card:=by positivity
  have hB0:(0:ℝ)≤B.card:=by positivity
  have hs:=hsize V U P D m hreg hn hD hρlo hρhi hm Q i hi
  have hNI:(N:ℝ)≤I.card:=by
    have he:0≤ε*(I.card:ℝ):=mul_nonneg hε.le hI0
    have hh:=hs.2.1
    change (N:ℝ)≤(1-ε)*I.card at hh
    nlinarith only [he,hh]
  have hconst:2*((3*d:ℕ):ℝ)≤(ζ/2)*I.card:=by
    have hN':2*((3*d:ℕ):ℝ)<(ζ/2)*(N:ℝ):=by
      have hh:2*((3*d:ℕ):ℝ)<(N:ℝ)*(ζ/2):=
        (div_lt_iff₀ (show 0<ζ/2 by positivity)).mp hN
      nlinarith only [hh]
    have hm:=mul_le_mul_of_nonneg_left hNI (show 0≤ζ/2 by positivity)
    linarith
  have hcap:δcap*min (I.card:ℝ) B.card≤(ζ/2)*I.card:=by
    calc
      _≤δcap*I.card:=mul_le_mul_of_nonneg_left (min_le_left _ _) hδcap
      _≤(ζ/2)*I.card:=mul_le_mul_of_nonneg_right hδζ hI0
  constructor
  · dsimp [L];exact add_nonneg (by positivity) (mul_nonneg hδcap (le_min hI0 hB0))
  · dsimp [L];nlinarith only [hconst,hcap]
end Oberwolfach
