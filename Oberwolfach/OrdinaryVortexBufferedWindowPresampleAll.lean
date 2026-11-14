module

public import Oberwolfach.OrdinaryVortexBufferedWindowPresampleCap

@[expose] public section
/-! One deterministic edit budget for every vortex level, chosen before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryVortexWindowEditBudget (d buffer:ℕ) (cost:ℕ→ℝ) (i:ℕ):ℝ :=
  if i=0 then 0 else 2*((3*d:ℕ):ℝ)+∑j∈Finset.Icc (i-1+2-buffer) (i-1),cost j

theorem ordinary_vortex_window_edit_budget_succ (d buffer:ℕ) (cost:ℕ→ℝ) (i:ℕ):
    ordinaryVortexWindowEditBudget d buffer cost (i+1)=
      2*((3*d:ℕ):ℝ)+∑j∈Finset.Icc (i+2-buffer) i,cost j :=by
  simp [ordinaryVortexWindowEditBudget]

theorem ordinary_vortex_buffered_window_presample_all
    (ε ρ₀ α pmin η ζ:ℝ) (d buffer:ℕ) (hbuffer:2≤buffer)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (hpmin1:pmin≤1)
    (hη:0<η) (hζ:0<ζ):
    ∃δ rate:ℝ,0<δ ∧ δ≤α ∧ 0<rate ∧ ∀β:ℝ,0≤β→β≤1/4→β≤δ→∀C:ℝ,0≤C→
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (cost:ℕ→ℝ),
      (∀i,i+1<Q.length→∀j∈Finset.Icc (i+2-buffer) i,0≤cost j ∧
        cost j≤4*rate*Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)+C)→
      ∀i,i<Q.length→0≤ordinaryVortexWindowEditBudget d buffer cost i ∧
        ordinaryVortexWindowEditBudget d buffer cost i≤ζ*(markedVortexInnerVertices Q i).card :=by
  obtain ⟨δ,rate,hδ,hδα,hrate,hcap⟩:=ordinary_vortex_buffered_window_presample_cap ε ρ₀ α pmin η ζ d buffer
    hbuffer hε hε1 hρ₀ hα hpmin hpmin1 hη hζ
  refine ⟨δ,rate,hδ,hδα,hrate,?_⟩
  intro β hβ hβ1 hβδ C hC
  obtain ⟨m₀,hm₀,hcap⟩:=hcap β hβ hβ1 hβδ C hC
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q cost hcost i hi
  cases i with
  | zero =>
    simp only [ordinaryVortexWindowEditBudget,if_true]
    exact ⟨le_rfl,mul_nonneg hζ.le (Nat.cast_nonneg _)⟩
  | succ i =>
    have hh:=hcap V U P D m hreg hn hD hρlo hρhi hm Q cost i (by omega) (hcost i (by omega))
    simpa only [ordinary_vortex_window_edit_budget_succ, Nat.succ_eq_add_one] using hh
end Oberwolfach
