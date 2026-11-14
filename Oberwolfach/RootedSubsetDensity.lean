module

public import Oberwolfach.RootedSubsetTails

@[expose] public section

/-! A dense ambient neighbourhood remains dense in a fixed-size sample,
including conditioning on a fixed set of at most a few vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rootedSubset_low_count {V : Type*} [Fintype V] [DecidableEq V]
    (T A : Finset V) (k : ℕ) (hk : T.card+k≤Fintype.card V) (hkpos : 0<k)
    [Nonempty (RootedSubset V T k)] [Nonempty (FixedSubset {x : V // x∉T} k)]
    (δ α : ℝ) (hα : 0<α)
    (hA : (δ+α)*Fintype.card V≤(A.card:ℝ))
    (hroots : (T.card:ℝ)≤α*(T.card+k:ℝ)/4) :
    (FiniteLaw.uniform (RootedSubset V T k)).probability
      (fun S => ((A∩S.val.val).card:ℝ)≤(δ+α/2)*(T.card+k:ℝ))≤
      2*Real.exp (-α^2*(T.card+k:ℝ)/8) := by
  have hn : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr (by omega)
  have hkr : (0:ℝ)<k := Nat.cast_pos.mpr hkpos
  have hm : (0:ℝ)<(T.card:ℝ)+k := by positivity
  have hscale : (δ+α)*(T.card+k:ℝ)≤(A.card:ℝ)*(T.card+k:ℝ)/Fintype.card V := by
    apply (le_div_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_right hA hm.le
    nlinarith only [hh]
  apply le_trans (finiteLaw_probability_mono _ _ _ ?_)
    (le_trans (rootedSubset_intersection_tail T A k hk hkpos (α*(T.card+k:ℝ)/4) (by positivity)) ?_)
  · intro S hS
    have hh := le_abs_self ((A.card:ℝ)*(T.card+k:ℝ)/Fintype.card V-
      ((A∩S.val.val).card:ℝ))
    rw [abs_sub_comm] at hh
    nlinarith [mul_nonneg hα.le hm.le]
  · apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    apply (div_le_iff₀ hkr).mpr
    have hh : 0≤α^2*((T.card:ℝ)+k)*T.card := by positivity
    nlinarith

theorem fixedSubset_containing_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) (m : ℕ) (hT : T.card≤m) (hm : m≤Fintype.card V) :
    Nonempty {S : FixedSubset V m // T⊆S.val} := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hT
  exact rootedSubset_nonempty T k hm

theorem fixedSubset_rooted_low_count {V : Type*} [Fintype V] [DecidableEq V]
    (T A : Finset V) (m : ℕ) (hT : T.card<m) (hm : m≤Fintype.card V)
    [Nonempty {S : FixedSubset V m // T⊆S.val}]
    (δ α : ℝ) (hα : 0<α) (hA : (δ+α)*Fintype.card V≤(A.card:ℝ))
    (hroots : (T.card:ℝ)≤α*m/4) :
    (FiniteLaw.uniform {S : FixedSubset V m // T⊆S.val}).probability
      (fun S => ((A∩S.val.val).card:ℝ)≤(δ+α/2)*m)≤
      2*Real.exp (-α^2*m/8) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hT.le
  have hk : 0<k := by omega
  letI : Nonempty (FixedSubset {x : V // x∉T} k) :=
    fixedSubset_nonempty (by
      rw [Fintype.card_subtype_compl]
      simp only [Fintype.card_coe]
      omega)
  simpa only [Nat.cast_add] using rootedSubset_low_count T A k hm hk δ α hα hA (by simpa only [Nat.cast_add] using hroots)

end Oberwolfach
