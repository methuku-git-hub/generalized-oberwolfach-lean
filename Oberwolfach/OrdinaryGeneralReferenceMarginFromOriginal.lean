module

public import Oberwolfach.Definitions
public import Mathlib.Tactic

@[expose] public section
/-! Reserve a positive margin for the all-level reference selector inside
an original ambient degree margin, before the finite host is chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_general_reference_margin_from_original
    (m:ℕ) (θ α₀:ℝ) (hθhalf:1/2≤θ) (hθcycle:cycleThreshold (m+1)≤θ)
    (hθ1:θ<1) (hα₀:0<α₀):
    ∃α:ℝ,0<α ∧ α≤1 ∧ max (1/2) (cycleThreshold (m+1))+α/4≤1 ∧
      cycleThreshold (m+1)+α≤θ+α₀ :=by
  let α:ℝ:=min (α₀/2) (min ((1-θ)/2) (1/2:ℝ))
  have ht:0<1-θ:=by linarith
  have hα:0<α:=by dsimp [α];positivity
  have hα₀':α≤α₀/2:=min_le_left _ _
  have hαθ:α≤(1-θ)/2:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hα1:α≤1/2:=le_trans (min_le_right _ _) (min_le_right _ _)
  have hθ:max (1/2) (cycleThreshold (m+1))≤θ:=max_le hθhalf hθcycle
  exact ⟨α,hα,by linarith,by linarith,by linarith⟩
theorem ordinary_regular_degree_margin_threshold_lt_one
    (V:Type) [Fintype V] (P:SimpleGraph V) [P.LocallyFinite] (D:ℕ) (θ α:ℝ)
    (v:V) (hreg:P.IsRegularOfDegree D) (hα:0<α)
    (hdegree:(θ+α)*Fintype.card V≤D):θ<1 :=by
  classical
  have hn:0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨v⟩
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hn
  have hD:D≤Fintype.card V:=by
    have hh:=Finset.card_le_univ (P.neighborFinset v)
    rw [SimpleGraph.card_neighborFinset_eq_degree,hreg v] at hh
    exact hh
  have hDR:(D:ℝ)≤Fintype.card V:=by exact_mod_cast hD
  by_contra hθ
  have hθge:1≤θ:=le_of_not_gt hθ
  have hprod:0≤(θ-1)*(Fintype.card V:ℝ):=mul_nonneg (by linarith) hnR.le
  have hprodα:0<α*(Fintype.card V:ℝ):=mul_pos hα hnR
  nlinarith only [hdegree,hDR,hprod,hprodα]
end Oberwolfach
