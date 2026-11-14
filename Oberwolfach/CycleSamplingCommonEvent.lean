module

public import Oberwolfach.CycleIndependentSampling
public import Oberwolfach.CommonEvents

@[expose] public section
/-! One original independent cycle sample controls every member of a fixed
finite family of vertex and pair tests. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {C J:Type} [Fintype C] [DecidableEq C]

theorem independent_cycle_sampling_common_event
    (p:C→ℝ) (hp:∀ c,0≤p c) (hp1:∀ c,p c≤1)
    (T:Finset J) (A:J→C→Prop) (ε:J→ℝ) (he:∀ j∈T,0≤ε j)
    (he1:∀ j∈T,ε j≤1):
    let μ:=FiniteLaw.pi (fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c))
    let mean:=fun j=>∑ c,if A j c then p c else 0
    1-∑ j∈T,2*Real.exp (-(ε j)^2*mean j/3)≤
      μ.probability (fun σ=>∀ j∈T,|independentCycleCount (A j) σ-mean j|<ε j*mean j) := by
  let μ:=FiniteLaw.pi (fun c=>FiniteLaw.retentionCoin (p c) (hp c) (hp1 c))
  let mean:=fun j=>∑ c,if A j c then p c else 0
  let bad:=fun j σ=>ε j*mean j≤|independentCycleCount (A j) σ-mean j|
  let bound:=fun j=>2*Real.exp (-(ε j)^2*mean j/3)
  have h:=finiteLaw_common_event_lower μ T bad bound (by
    intro j hj
    exact independent_cycle_count_chernoff p hp hp1 (A j) (ε j) (he j hj) (he1 j hj))
  simpa only [bad,not_le] using h
end Oberwolfach
