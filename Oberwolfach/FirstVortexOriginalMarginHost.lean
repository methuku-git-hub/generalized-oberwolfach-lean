module

public import Oberwolfach.FirstVortexSharedHostVortexTrimDistinctWeights
public import Oberwolfach.PrunedLongClassIndependentDensity

@[expose] public section
/-! Choose the reference margin and long-class density threshold from the
original degree margin, before the later short-class cutoff and K. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem first_vortex_original_margin_host
    (α:ℝ) (hα:0<α):
    ∃ (αRef κL ρ₀:ℝ) (href:0<αRef) (hρ:0<ρ₀), 2*αRef≤1 ∧ 2*αRef≤α/2 ∧
      0<κL ∧ κL≤α/1000 ∧ ρ₀≤1 ∧ ρ₀≤2*κL ∧
      (∀δ D:ℝ,∀n:ℕ,(δ+α/2)*(n:ℝ)≤D→(δ+2*αRef)*(n:ℝ)≤D) ∧
    ∀L₀:ℕ,
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      1/(100*((r+4:ℕ):ℝ))≤βList/16 ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
      (∀K d:ℕ,0<K→2≤d→
        ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ HostMatchingVortexContinuation m K d (2*αRef) A BM BO) ∧
      FirstVortexSharedVortexTailDistinctWeights r k₀ αRef ρ₀ href hρ :=by
  let αRef:=min (α/8) (1/4:ℝ)
  let κL:=α/2000
  let ρ₀:=min κL (1/2:ℝ)
  have href:0<αRef:=by dsimp [αRef]; positivity
  have hrefCap:2*αRef≤1:=by have h:=min_le_right (α/8) (1/4:ℝ);dsimp only [αRef];linarith
  have hrefAlpha:2*αRef≤α/2:=by have h:=min_le_left (α/8) (1/4:ℝ);dsimp only [αRef];linarith
  have hκ:0<κL:=by dsimp [κL]; positivity
  have hκcap:κL≤α/1000:=by dsimp [κL];linarith
  have hρ:0<ρ₀:=by dsimp [ρ₀];positivity
  have hρone:ρ₀≤1:=by have h:=min_le_right κL (1/2:ℝ);dsimp only [ρ₀];linarith
  have hρκ:ρ₀≤2*κL:=by have h:=min_le_left κL (1/2:ℝ);dsimp only [ρ₀];linarith
  refine ⟨αRef,κL,ρ₀,href,hρ,hrefCap,hrefAlpha,hκ,hκcap,hρone,hρκ,?_,?_⟩
  · intro δ D n hD
    have hn:0≤(n:ℝ):=by positivity
    nlinarith
  · intro L₀ βList
    exact first_vortex_shared_host_vortex_trim_distinct_weights L₀ αRef ρ₀ href hrefCap hρ hρone
end Oberwolfach
