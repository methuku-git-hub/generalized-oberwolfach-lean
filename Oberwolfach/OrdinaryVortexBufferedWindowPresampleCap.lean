module

public import Oberwolfach.OrdinaryVortexBufferedCostGeometry
public import Oberwolfach.OrdinaryVortexCleanupCanonicalCap

@[expose] public section
/-! The recent-window edit budget can be fixed from the vortex and cost
schedule before the random wheel outcome or protected trace is revealed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_buffered_window_presample_cap
    (ε ρ₀ α pmin η ζ:ℝ) (d buffer:ℕ) (hbuffer:2≤buffer)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (hpmin1:pmin≤1)
    (hη:0<η) (hζ:0<ζ):
    ∃δ rate:ℝ,0<δ ∧ δ≤α ∧ 0<rate ∧ ∀β:ℝ,0≤β→β≤1/4→β≤δ→∀C:ℝ,0≤C→
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (cost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
      (∀j∈Finset.Icc (i+2-buffer) i,0≤cost j ∧
        cost j≤4*rate*Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)+C)→
    let Ledit:=2*((3*d:ℕ):ℝ)+∑j∈Finset.Icc (i+2-buffer) i,cost j;
    0≤Ledit ∧ Ledit≤ζ*(markedVortexInnerVertices Q (i+1)).card :=by
  obtain ⟨δ,hδ,hδα,hδζ,hcap⟩:=ordinary_vortex_cleanup_canonical_cap ε ρ₀ α pmin pmin η ζ d
    hε hε1 hρ₀ hα hpmin hpmin hη hζ
  obtain ⟨rate,hrate,hcost⟩:=ordinary_vortex_buffered_cost_from_geometry ε ρ₀ δ buffer hbuffer hε hε1 hρ₀ hδ
  refine ⟨δ,rate,hδ,hδα,hrate,?_⟩
  intro β hβ hβ1 hβδ C hC
  obtain ⟨ma,hma,hcap⟩:=hcap β hβ hβ1 hβδ
  obtain ⟨mb,hmb,hcost⟩:=hcost β hβ hβ1 C hC
  refine ⟨max ma mb,by omega,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q cost i hi hcosts Ledit
  have hwin:=hcost V U P D m hreg hn hD hρlo hρhi (by omega) Q i hi cost hcosts
  have hnum:=hcap V U P D m hreg hn hD hρlo hρhi (by omega) Q (i+1) hi pmin pmin (1/2) 0 0 0 0
    le_rfl hpmin1 le_rfl (by norm_num) (by norm_num) hδ.le (by norm_num) hδ.le
    (by norm_num) hδ.le (by norm_num) hδ.le
  let I:=markedVortexInnerVertices Q (i+1)
  let B:=markedVortexInnerHubs Q (i+1)
  have hI:0≤(I.card:ℝ):=by positivity
  have hB:0≤(B.card:ℝ):=by positivity
  have hwinCap:(∑j∈Finset.Icc (i+2-buffer) i,cost j)≤δ*min (I.card:ℝ) B.card:=by
    rcases le_total (I.card:ℝ) B.card with hh | hh
    · rw [min_eq_left hh];exact hwin.2.1
    · rw [min_eq_right hh];exact hwin.2.2
  have hL: Ledit≤ζ*I.card:=by
    have hh:=hnum.2.2.2.2.1
    dsimp [Ledit]
    linarith only [hwinCap,hh]
  have hsum0:0≤∑j∈Finset.Icc (i+2-buffer) i,cost j:=by
    exact Finset.sum_nonneg (fun j hj => (hcosts j hj).1)
  exact ⟨by dsimp [Ledit];positivity,hL⟩
end Oberwolfach
