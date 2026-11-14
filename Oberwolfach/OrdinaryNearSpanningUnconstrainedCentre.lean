module

public import Oberwolfach.OrdinaryAlmostRegularNearSpanningCycles
public import Oberwolfach.ThresholdComparisons

@[expose] public section
/-! The centre of the almost-regular degree interval need not be assumed
feasible: it can be clamped to the range of graph degrees. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_above_threshold_near_spanning_cycles
    (r:ℕ) (hr:3≤r) (α ε:ℝ) (hα:0<α) (hε:0<ε):
    ∃ η:ℝ,0<η ∧ ∃ N:ℕ,
    ∀ (V:Type) [Fintype V] [DecidableEq V] (G:SimpleGraph V),
      N≤Fintype.card V→
      (∀ v,(cycleThreshold r+α)*Fintype.card V≤(G.degree v:ℝ))→
      (∃ d:ℝ,∀ v,|(G.degree v:ℝ)-d|≤η*(Fintype.card V:ℝ))→
      ∃ M:Finset (OrdinaryCycle G r),
        (∀ C∈M,∀ C'∈M,C≠C'→Disjoint C.val.val.support.toFinset C'.val.val.support.toFinset) ∧
        (1-ε)*Fintype.card V≤(r:ℝ)*M.card := by
  obtain ⟨η₀,hη₀,N₀,hpack⟩:=ordinary_above_threshold_almost_regular_near_spanning_cycles r hr α ε hα hε
  let η:=min η₀ (α/4)
  have hη:0<η:=by dsimp [η];positivity
  have hη0:η≤η₀:=min_le_left _ _
  have hηα:η≤α/4:=min_le_right _ _
  refine ⟨η,hη,max 1 N₀,?_⟩
  intro V _ _ G hn hdeg ⟨d,hreg⟩
  have hn0:0<Fintype.card V:=by omega
  have hnpos:0<(Fintype.card V:ℝ):=by exact_mod_cast hn0
  letI:Nonempty V:=Fintype.card_pos_iff.mp hn0
  let v:V:=Classical.choice inferInstance
  have hhalf:(1/2:ℝ)≤cycleThreshold r:=cycleThreshold_half_le hr
  have hdeglo:(1/2+α)*(Fintype.card V:ℝ)≤(G.degree v:ℝ):=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2+α:ℝ)≤cycleThreshold r+α by linarith) hnpos.le
    exact hh.trans (hdeg v)
  have hregv:-(η*(Fintype.card V:ℝ))≤(G.degree v:ℝ)-d:=(abs_le.mp (hreg v)).1
  have hdiff:(G.degree v:ℝ)-d≤η*(Fintype.card V:ℝ):=(abs_le.mp (hreg v)).2
  have hηn:=mul_le_mul_of_nonneg_right hηα hnpos.le
  have hdlo:(Fintype.card V:ℝ)/2≤d:=by nlinarith
  let d':=min d (Fintype.card V:ℝ)
  have hd'lo:(Fintype.card V:ℝ)/2≤d' := by dsimp [d'];apply le_min hdlo;linarith
  have hd'hi:d'≤Fintype.card V := min_le_right _ _
  have hregular:∀ u,|(G.degree u:ℝ)-d'|≤η₀*(Fintype.card V:ℝ) := by
    intro u
    have hdegup:(G.degree u:ℝ)≤Fintype.card V := by
      exact_mod_cast (Nat.le_of_lt (G.degree_lt_card_verts u))
    have hreg0:|(G.degree u:ℝ)-d|≤η₀*(Fintype.card V:ℝ) :=
      (hreg u).trans (mul_le_mul_of_nonneg_right hη0 hnpos.le)
    by_cases hd:d≤Fintype.card V
    · simpa [d',min_eq_left hd] using hreg0
    · have hnd:(Fintype.card V:ℝ)≤d:=le_of_not_ge hd
      have h1:(G.degree u:ℝ)≤d:=hdegup.trans hnd
      dsimp [d']
      rw [min_eq_right hnd,abs_of_nonpos (sub_nonpos.mpr hdegup),abs_of_nonpos (sub_nonpos.mpr h1)] at *
      linarith
  exact hpack V G ((le_max_right 1 N₀).trans hn) d' hd'lo hd'hi hdeg hregular
end Oberwolfach
