module

public import Oberwolfach.OrdinaryTransferConfigurations
public import Oberwolfach.OrdinaryCycleRootCounts

@[expose] public section

/-! Coefficient and support bounds for the actual transfer configurations.
The counting argument uses only their injective free-label maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem transferCycleCoefficient_abs_sum {r : ℕ} (hr : 0<r) :
    (∑ j : TransferCycleIndex r,|transferCycleCoefficient j|)≤3 := by
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have habs (j : TransferCycleIndex r) : |transferCycleCoefficient j|=1/(r:ℝ) := by
    rcases j with ⟨⟩|⟨i,b⟩
    · simp [transferCycleCoefficient,abs_of_nonneg (show 0≤1/(r:ℝ) by positivity)]
    · cases b <;> simp [transferCycleCoefficient,abs_of_nonneg (show 0≤1/(r:ℝ) by positivity)]
  simp only [habs,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_sum,Fintype.card_unique,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  push_cast
  have h1 : (1:ℝ)≤r := by exact_mod_cast hr
  rw [mul_one_div]
  apply (div_le_iff₀ hr').mpr
  linarith

theorem indexedWheelWeight_abs_le {V U I : Type*} [Fintype I]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : I → OrdinaryWheel Q F H r) (a : I → ℝ) (D : OrdinaryWheel Q F H r) :
    |indexedWheelWeight W a D|≤∑ i,|a i| := by
  unfold indexedWheelWeight
  apply (Finset.abs_sum_le_sum_abs (fun i => if W i=D then a i else 0) Finset.univ).trans
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · rfl
  · simpa only [abs_zero] using abs_nonneg (a i)

theorem indexedWheelWeight_zero_of_no_image {V U I : Type*} [Fintype I]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : I → OrdinaryWheel Q F H r) (a : I → ℝ) (D : OrdinaryWheel Q F H r)
    (hD : ∀ i,W i≠D) : indexedWheelWeight W a D=0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (hD i)

theorem OrdinaryTransferConfiguration.coefficient_bound {V U : Type*} {r : ℕ} {hr : 3≤r}
    {Q F : SimpleGraph V} {H : V → U → Prop} {v : V} {u u' : U}
    (T : OrdinaryTransferConfiguration hr Q F H v u u') (D : OrdinaryWheel Q F H r) :
    |T.weight D|≤6 := by
  have h₁ := (indexedWheelWeight_abs_le (T.wheel true) transferCycleCoefficient D).trans
    (transferCycleCoefficient_abs_sum (by omega))
  have h₂ := (indexedWheelWeight_abs_le (T.wheel false) transferCycleCoefficient D).trans
    (transferCycleCoefficient_abs_sum (by omega))
  have hh := abs_add_le (indexedWheelWeight (T.wheel true) transferCycleCoefficient D)
    (-(indexedWheelWeight (T.wheel false) transferCycleCoefficient D))
  simp only [abs_neg,← sub_eq_add_neg] at hh
  change |indexedWheelWeight (T.wheel true) transferCycleCoefficient D-
    indexedWheelWeight (T.wheel false) transferCycleCoefficient D|≤6
  linarith

theorem OrdinaryTransferConfiguration.weight_support {V U : Type*} {r : ℕ} {hr : 3≤r}
    {Q F : SimpleGraph V} {H : V → U → Prop} {v : V} {u u' : U}
    (T : OrdinaryTransferConfiguration hr Q F H v u u') (D : OrdinaryWheel Q F H r)
    (hD : T.weight D≠0) :
    (ordinaryWheelHub D=u ∨ ordinaryWheelHub D=u') ∧
      (ordinaryWheelRim D).support⊆insert v (Set.range T.labels) := by
  have hex : ∃ b : Bool,∃ j : TransferCycleIndex r,T.wheel b j=D := by
    by_contra hn
    have hzero (b : Bool) : indexedWheelWeight (T.wheel b) transferCycleCoefficient D=0 := by
      apply indexedWheelWeight_zero_of_no_image
      intro j hj
      exact hn ⟨b,j,hj⟩
    apply hD
    change indexedWheelWeight (T.wheel true) transferCycleCoefficient D-
      indexedWheelWeight (T.wheel false) transferCycleCoefficient D=0
    rw [hzero,hzero,sub_self]
  obtain ⟨b,j,rfl⟩ := hex
  constructor
  · cases b
    · exact Or.inr rfl
    · exact Or.inl rfl
  · exact transferCycleGraph_support_subset hr T.labels v T.omitted j

end Oberwolfach
