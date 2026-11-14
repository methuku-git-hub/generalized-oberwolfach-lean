module

public import Oberwolfach.OrdinaryRimCorrection
public import Oberwolfach.OrdinarySpokeCorrection

@[expose] public section

/-! Exact ordinary wheel loads from the two actual correction constructions.
The displayed norm bound is used to retain the original positive baseline. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryWheelCorrectionConstant (r : ℕ) (γ : ℝ) : ℝ :=
  (r+1)^2/γ+2*(1+1/γ)*(6*((r:ℝ)^2)^r/γ)*(r+1)

theorem ordinaryWheelCorrectionConstant_pos (r : ℕ) (γ : ℝ) (hγ : 0<γ) :
    0<ordinaryWheelCorrectionConstant r γ := by
  unfold ordinaryWheelCorrectionConstant
  positivity

theorem ordinary_wheel_correction (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V U : Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      ∀ (P Q F : SimpleGraph V) (H : V → U → Prop) (k : ℕ),N≤k →
      ∀ θ : ℝ,cycleThreshold r≤θ → ∀ γ η : ℝ,0<γ → 0≤η →
      0<Fintype.card V → Q≤P →
      (∀ v,Q.degree v=2*(Finset.univ.filter (H v)).card) →
      (∀ x y,Q.Adj x y → γ*(Fintype.card V:ℝ)^(k-1)≤
        (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ)) →
      (∀ v (i j : {u // H v u}),i.val≠j.val →
        γ*(Fintype.card V:ℝ)^(r^2)≤
          (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ)) →
      ∀ ψ : OrdinaryWheel Q F H r → ℝ,
      (∀ x y,|ordinaryRimResidual ψ x y|≤η) →
      (∀ v u,|ordinarySpokeResidual ψ v u|≤η) →
      ∃ ω : OrdinaryWheel Q F H r → ℝ,
        (∀ x y,ordinaryRimLoad ω x y=if Q.Adj x y then 1 else 0) ∧
        (∀ v u,ordinarySpokeLoad ω v u=if H v u then 1 else 0) ∧
        (∀ D,|ω D-ψ D|≤ordinaryWheelCorrectionConstant r γ*η/(Fintype.card V:ℝ)^(r-1)) := by
  obtain ⟨N,hN⟩ := ordinary_rim_correction r hr α hα
  refine ⟨N,?_⟩
  intro V U _ _ _ _ P Q F H k hk θ hθ γ η hγ hη hn hQP hdeg hcount hT ψ hRerr hSerr
  obtain ⟨R,hR,hRb,hRs⟩ := hN V U P Q F H k hk θ hθ γ η hγ hη hn hQP hcount ψ hRerr
  let ψ₁ (D : OrdinaryWheel Q F H r) : ℝ := ψ D+R D
  have hR₁ (x y : V) : ordinaryRimLoad ψ₁ x y=if Q.Adj x y then 1 else 0 := by
    change ordinaryRimLoad (ψ+R) x y=if Q.Adj x y then 1 else 0
    rw [ordinaryRimLoad_add ψ R x y,hR,ordinaryRimResidual]
    ring
  have hS₁ (v : V) (u : U) : |ordinarySpokeResidual ψ₁ v u|≤η*(1+1/γ) := by
    have he : ordinarySpokeResidual ψ₁ v u=
        ordinarySpokeResidual ψ v u-ordinarySpokeLoad R v u := by
      change (if H v u then (1:ℝ) else 0)-ordinarySpokeLoad (ψ+R) v u=
        ((if H v u then (1:ℝ) else 0)-ordinarySpokeLoad ψ v u)-ordinarySpokeLoad R v u
      rw [ordinarySpokeLoad_add ψ R v u]
      ring
    rw [he]
    calc
      _ ≤ |ordinarySpokeResidual ψ v u|+|ordinarySpokeLoad R v u| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (ordinarySpokeResidual ψ v u) (-ordinarySpokeLoad R v u)
      _ ≤ η+η/γ := add_le_add (hSerr v u) (hRs v u)
      _ = _ := by ring
  obtain ⟨S,hSR,hSS,hSb⟩ := ordinary_spoke_correction hr Q F H γ (η*(1+1/γ))
    hγ (by positivity) hn ψ₁ hdeg (fun x y hxy => by simpa only [if_pos hxy] using hR₁ x y) hS₁ hT
  let ω (D : OrdinaryWheel Q F H r) : ℝ := ψ₁ D+S D
  refine ⟨ω,?_,?_,?_⟩
  · intro x y
    change ordinaryRimLoad (ψ₁+S) x y=if Q.Adj x y then 1 else 0
    rw [ordinaryRimLoad_add ψ₁ S x y,hSR,add_zero]
    exact hR₁ x y
  · intro v u
    change ordinarySpokeLoad (ψ₁+S) v u=if H v u then 1 else 0
    rw [ordinarySpokeLoad_add ψ₁ S v u,hSS,ordinarySpokeResidual]
    ring
  · intro D
    have he : ω D-ψ D=R D+S D := by dsimp [ω,ψ₁];ring
    rw [he]
    calc
      _ ≤ |R D|+|S D| := abs_add_le _ _
      _ ≤ η*(r+1)^2/(γ*(Fintype.card V:ℝ)^(r-1))+
          (2*(η*(1+1/γ))*(6*((r:ℝ)^2)^r/γ)*(r+1))/(Fintype.card V:ℝ)^(r-1) :=
        add_le_add (hRb D) (hSb D)
      _ = _ := by unfold ordinaryWheelCorrectionConstant;ring

end Oberwolfach
