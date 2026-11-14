module

public import Oberwolfach.MarkedSpokeColumnResidual
public import Oberwolfach.MarkedAlternatingCorrection

@[expose] public section

/-! Complete correction of both spoke types after exact rim loads. The
column correction is followed by the proved sparse four-cycle correction
and its actual four-wheel realization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedSpokeCorrectionConstant (m : ℕ) (β L : ℝ) : ℝ :=
  4/β+8*(8*L^3*(1+9*L^3))*(1+4*(m+1)/β)/β

theorem marked_spoke_correction {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (β η L δ D : ℝ) (hβ : 0<β) (hη : 0≤η) (hn : 0<Fintype.card V) (hu : 0<Fintype.card U)
    (p q : Bool → U → ℝ)
    (hdata : ∀ j,SparseIntersectionData (if j then Hₖ else H₀) (p j) (q j) L δ D)
    (hsmall : δ+D/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤1/(200*L^6))
    (i : Bool → Fin (m+1)) (hipos : ∀ j,markedPositionType (i j)=j)
    (hcommon : ∀ u u' : U,u≠u' → β*(Fintype.card V:ℝ)^(m+1)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u'):ℝ))
    (hpaths : ∀ j,∀ Q : BipartiteFourCycle (if j then Hₖ else H₀),
      β*(Fintype.card V:ℝ)^m≤
      (Fintype.card (MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ))
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (hrow : ∀ j v,(∑ u,markedSpokeResidual ψ j v u)=0)
    (hcol : ∀ u,(∑ v,markedSpokeResidual ψ false v u)=(m:ℝ)*(∑ v,markedSpokeResidual ψ true v u))
    (herr : ∀ j v u,|markedSpokeResidual ψ j v u|≤η) :
    ∃ Φ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad Φ e=0) ∧
      (∀ j v u,markedWheelSpokeLoad Φ j v u=markedSpokeResidual ψ j v u) ∧
      (∀ W,|Φ W|≤markedSpokeCorrectionConstant m β L*η/(Fintype.card V:ℝ)^m) := by
  have hL := (hdata false).L_nonneg
  let C := 8*L^3*(1+9*L^3)
  let A := 1+4*(m+1)/β
  have hC : 0≤C := by dsimp [C];positivity
  have hA : 0≤A := by dsimp [A];positivity
  obtain ⟨Ψ,hΨrim,hΨcoeff,hres,hresnorm⟩ :=
    marked_spoke_column_residual β η hβ hη hn hcommon ψ hrow hcol herr
  let r (j : Bool) (e : V×U) := markedSpokeResidual ψ j e.1 e.2-markedWheelSpokeLoad Ψ j e.1 e.2
  have hex (j : Bool) : ∃ Φ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad Φ e=0) ∧
      (∀ k v u,markedWheelSpokeLoad Φ k v u=if j=k then r j (v,u) else 0) ∧
      (∀ W,|Φ W|≤4*(C*A*η)/(β*(Fintype.card V:ℝ)^m)) := by
    obtain ⟨a,hrep,hload⟩ := sparse_alternating_correction_inverse_profile
      (if j then Hₖ else H₀) (p j) (q j) L δ D (hdata j) hn hu hsmall (r j) (hres j)
    have hl (e : V×U) : (∑ Q,if FourCycleIncident Q e then |a Q| else 0)≤C*A*η := by
      calc
        _ ≤ C*‖r j‖ := hload e
        _ ≤ C*(A*η) := mul_le_mul_of_nonneg_left (hresnorm j) hC
        _ = _ := by ring
    exact marked_alternating_correction (i j) j (hipos j) β (C*A*η) hβ (by positivity) hn
      (hpaths j) (r j) a hrep hl
  choose Γ hΓrim hΓspoke hΓcoeff using hex
  let χ (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) := ∑ j : Bool,(1:ℝ)*Γ j W
  refine ⟨Ψ+χ,?_,?_,?_⟩
  · intro e
    rw [markedWheelRimLoad_add,hΨrim,zero_add]
    unfold χ
    rw [markedWheelRimLoad_combination]
    simp only [hΓrim,mul_zero,Finset.sum_const_zero]
  · intro j v u
    rw [markedWheelSpokeLoad_add]
    have hχ : markedWheelSpokeLoad χ j v u=r j (v,u) := by
      unfold χ
      rw [markedWheelSpokeLoad_combination]
      simp only [hΓspoke,one_mul]
      cases j <;> simp
    rw [hχ]
    dsimp only [r]
    ring
  · intro W
    have hχ : |χ W|≤2*(4*(C*A*η)/(β*(Fintype.card V:ℝ)^m)) := by
      calc
        _ ≤ ∑ j : Bool,|(1:ℝ)*Γ j W| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Bool,4*(C*A*η)/(β*(Fintype.card V:ℝ)^m) := by
          apply Finset.sum_le_sum;intro j _;simpa only [one_mul] using hΓcoeff j W
        _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_bool,nsmul_eq_mul,Nat.cast_ofNat]
    calc
      _ ≤ |Ψ W|+|χ W| := abs_add_le _ _
      _ ≤ 4*η/(β*(Fintype.card V:ℝ)^m)+2*(4*(C*A*η)/(β*(Fintype.card V:ℝ)^m)) :=
        add_le_add (hΨcoeff W) hχ
      _ = _ := by dsimp only [markedSpokeCorrectionConstant,C,A];ring

end Oberwolfach
