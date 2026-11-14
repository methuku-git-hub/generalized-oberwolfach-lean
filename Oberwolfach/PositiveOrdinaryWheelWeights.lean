module

public import Oberwolfach.OrdinaryWheelCorrection

@[expose] public section

/-! Positive ordinary wheel weights. The constants are fixed before the
host graphs and the initial weighting. No correction or matching statement
is taken as an unproved input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem positive_ordinary_wheel_weights (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ k : ℕ,N≤k → ∀ θ γ bminus bplus : ℝ,
      max (1/2) (cycleThreshold r)≤θ → 0<γ → 0<bminus → 0<bplus →
      ∃ η₀ : ℝ,0<η₀ ∧
      ∀ (V U : Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      0<Fintype.card V → Fintype.card U≤Fintype.card V →
      ∀ (P Q F : SimpleGraph V) (H : V → U → Prop),Q≤P\F →
      (∀ v,Q.degree v=2*(Finset.univ.filter (H v)).card) →
      (∀ v,γ*Fintype.card V≤((Finset.univ.filter (H v)).card:ℝ)) →
      (∀ x y,Q.Adj x y → γ*(Fintype.card V:ℝ)^(k-1)≤
        (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ (α/4) x y):ℝ)) →
      (∀ v (i j : {u // H v u}),i.val≠j.val →
        γ*(Fintype.card V:ℝ)^(r^2)≤
          (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ)) →
      ∀ η : ℝ,0≤η → η≤η₀ → ∀ ψ : OrdinaryWheel Q F H r → ℝ,
      (∀ D,bminus/(Fintype.card V:ℝ)^(r-1)≤ψ D ∧
        ψ D≤bplus/(Fintype.card V:ℝ)^(r-1)) →
      (∀ x y,Q.Adj x y → |ordinaryRimLoad ψ x y-1|≤η) →
      (∀ v u,H v u → |ordinarySpokeLoad ψ v u-1|≤η) →
      ∃ ω : OrdinaryWheel Q F H r → ℝ,
        (∀ x y,ordinaryRimLoad ω x y=if Q.Adj x y then 1 else 0) ∧
        (∀ v u,ordinarySpokeLoad ω v u=if H v u then 1 else 0) ∧
        (∀ D,(bminus/2)/(Fintype.card V:ℝ)^(r-1)≤ω D ∧
          ω D≤(bplus+bminus/2)/(Fintype.card V:ℝ)^(r-1)) := by
  obtain ⟨N,hN⟩ := ordinary_wheel_correction r hr (α/4) (by positivity)
  refine ⟨N,?_⟩
  intro k hk θ γ bminus bplus hθ hγ hbm _hbp
  let C := ordinaryWheelCorrectionConstant r γ
  have hC : 0<C := ordinaryWheelCorrectionConstant_pos r γ hγ
  refine ⟨bminus/(2*C),by positivity,?_⟩
  intro V U _ _ _ _ hn _hU P Q F H hQP hdeg _hH hcount hT η hη hη₀ ψ hψ hR hS
  have hRerr (x y : V) : |ordinaryRimResidual ψ x y|≤η := by
    by_cases hxy : Q.Adj x y
    · simp only [ordinaryRimResidual,if_pos hxy,abs_sub_comm]
      exact hR x y hxy
    · rw [ordinaryRimResidual_outside ψ x y hxy,abs_zero]
      exact hη
  have hSerr (v : V) (u : U) : |ordinarySpokeResidual ψ v u|≤η := by
    by_cases hvu : H v u
    · simp only [ordinarySpokeResidual,if_pos hvu,abs_sub_comm]
      exact hS v u hvu
    · rw [ordinarySpokeResidual_outside ψ v u hvu,abs_zero]
      exact hη
  obtain ⟨ω,hωR,hωS,hωb⟩ := hN V U P Q F H k hk θ ((le_max_right _ _).trans hθ)
    γ η hγ hη hn (hQP.trans sdiff_le) hdeg hcount hT ψ hRerr hSerr
  have hsmall : C*η≤bminus/2 := by
    have hh := (le_div_iff₀ (show 0<2*C by positivity)).mp hη₀
    nlinarith
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  refine ⟨ω,hωR,hωS,?_⟩
  intro D
  have hdiff : |ω D-ψ D|≤(bminus/2)/(Fintype.card V:ℝ)^(r-1) :=
    (hωb D).trans (div_le_div_of_nonneg_right hsmall (by positivity))
  have hh := abs_le.mp hdiff
  have hlow := (hψ D).1
  have hhigh := (hψ D).2
  constructor
  · have he : bminus/(Fintype.card V:ℝ)^(r-1)=
        2*((bminus/2)/(Fintype.card V:ℝ)^(r-1)) := by ring
    linarith
  · rw [add_div]
    linarith

end Oberwolfach
