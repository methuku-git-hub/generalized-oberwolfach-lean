module

public import Oberwolfach.OrdinaryCycleApproximation
public import Oberwolfach.OrdinaryPositiveScales

@[expose] public section

/-! Positive bounded ordinary cycle weights. The constants and order threshold
are chosen before the graph and before its supplied edge-load vector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem positive_ordinary_cycle_weights (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ ε c C : ℝ,0<ε ∧ 0<c ∧ 0<C ∧ ∃ N : ℕ,0<N ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ G : SimpleGraph V,
        (∀ v,(cycleThreshold r+α)*Fintype.card V≤(G.degree v:ℝ)) →
      ∀ w : G.edgeSet → ℝ,‖w-(fun _ => (1:ℝ))‖≤ε →
      ∃ a : OrdinaryCycle G r → ℝ,
        (∀ D,c/(Fintype.card V:ℝ)^(r-2)≤a D ∧
          a D≤C/(Fintype.card V:ℝ)^(r-2)) ∧
        (∑ D,a D • ordinaryCycleIncidence G r D)=w := by
  let κ := min (1/2:ℝ) (α/32)
  have hκ : 0<κ := lt_min (by norm_num) (by positivity)
  have hκ1 : κ≤1 := (min_le_left _ _).trans (by norm_num)
  have hκα : κ≤α/16 := (min_le_right _ _).trans (by linarith)
  obtain ⟨N₀,hN₀⟩ := ordinary_cycle_approximation_at_size r hr α hα
  obtain ⟨m,hm₀,hm4,hmroots,hmerr⟩ := ordinary_positive_sample_size N₀ α κ hα hκ
  let c := κ/(4*(r:ℝ)^2)
  let C := c+4*(m:ℝ)^(r-2)
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr (by omega)
  have hc : 0<c := by dsimp [c];positivity
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨κ/4,c,C,by positivity,hc,hC,m,by omega,?_⟩
  intro V _ _ hn G hdeg w hw
  obtain ⟨a,ha,he⟩ := exact_positive_ordinary_cycle_weights G r (by omega) (by omega)
    w κ (8*m*Real.exp (-α^2*m/32)) (4*(m:ℝ)^(r-2)) hκ hmerr hw
    (fun w' hw' => hN₀ m hm₀ hm4 hmroots V hn G hdeg κ hκ.le hκ1 hκα w' hw')
  exact ⟨a,fun D => ⟨(ha D).2.1,(ha D).2.2⟩,he⟩

theorem positive_ordinary_fractional_cycle_weights (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∃ N : ℕ,0<N ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ G : SimpleGraph V,
        (∀ v,(cycleThreshold r+α)*Fintype.card V≤(G.degree v:ℝ)) →
      ∃ a : OrdinaryCycle G r → ℝ,
        (∀ D,c/(Fintype.card V:ℝ)^(r-2)≤a D ∧
          a D≤C/(Fintype.card V:ℝ)^(r-2)) ∧
        (∀ e : G.edgeSet,∑ D,a D*ordinaryCycleIncidence G r D e=1) := by
  obtain ⟨ε,c,C,hε,hc,hC,N,hN,hh⟩ := positive_ordinary_cycle_weights r hr α hα
  refine ⟨c,C,hc,hC,N,hN,?_⟩
  intro V _ _ hn G hdeg
  obtain ⟨a,ha,he⟩ := hh V hn G hdeg (fun _ => 1) (by simpa using hε.le)
  refine ⟨a,ha,?_⟩
  intro e
  have h := congrFun he e
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using h

end Oberwolfach
