module

public import Oberwolfach.OrdinaryAveragedIsolatorExistence
public import Oberwolfach.OrdinaryRimCorrectionBounds

@[expose] public section

/-! The complete rim correction, obtained from actual admissible induced
subgraphs. Both its wheel coefficients and its new spoke errors are bounded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_rim_correction (r : ℕ) (hr : 3≤r) (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V U : Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      ∀ (P Q F : SimpleGraph V) (H : V → U → Prop) (k : ℕ),N≤k →
      ∀ θ : ℝ,cycleThreshold r≤θ → ∀ γ η : ℝ,0<γ → 0≤η →
      0<Fintype.card V → Q≤P →
      (∀ x y,Q.Adj x y → γ*(Fintype.card V:ℝ)^(k-1)≤
        (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ)) →
      ∀ ψ : OrdinaryWheel Q F H r → ℝ,
      (∀ x y,|ordinaryRimResidual ψ x y|≤η) →
      ∃ Φ : OrdinaryWheel Q F H r → ℝ,
        (∀ x y,ordinaryRimLoad Φ x y=ordinaryRimResidual ψ x y) ∧
        (∀ D,|Φ D|≤η*(r+1)^2/(γ*(Fintype.card V:ℝ)^(r-1))) ∧
        (∀ v u,|ordinarySpokeLoad Φ v u|≤η/γ) := by
  obtain ⟨N,hN⟩ := ordinary_averaged_isolator_exists r hr α hα
  refine ⟨N,?_⟩
  intro V U _ _ _ _ P Q F H k hk θ hθ γ η hγ hη hn hQP hcount ψ herr
  have hex (x y : V) : ∃ I : OrdinaryWheel Q F H r → ℝ,
      (¬Q.Adj x y → ∀ D,I D=0) ∧
      (Q.Adj x y → ∀ a b,ordinaryRimLoad I a b=
        if (SimpleGraph.edge x y).Adj a b then 1 else 0) ∧
      (∀ D,|I D|≤1/(γ*(Fintype.card V:ℝ)^
        (((ordinaryWheelRim D).support.toFinset∪{x,y}).card-1))) ∧
      (∀ v u,|ordinarySpokeLoad I v u|≤
        (if v=x ∨ v=y then (1:ℝ) else 0)/(2*γ*Fintype.card V)) := by
    by_cases hxy : Q.Adj x y
    · obtain ⟨I,hR,hb,hs⟩ := hN V U P Q F H k hk θ hθ γ hγ hn x y (hQP hxy) (hcount x y hxy)
      exact ⟨I,(fun hn => False.elim (hn hxy)),(fun _ => hR),hb,hs⟩
    · refine ⟨fun _ => 0,(fun _ _ => rfl),(fun h => False.elim (hxy h)),?_,?_⟩
      · intro D;rw [abs_zero];positivity
      · intro v u
        simp only [ordinarySpokeLoad,ite_self,Finset.sum_const_zero,abs_zero]
        positivity
  choose I hzero hload hbound hspoke using hex
  let Φ (D : OrdinaryWheel Q F H r) : ℝ :=
    ∑ p : V×V,(ordinaryRimResidual ψ p.1 p.2/2)*I p.1 p.2 D
  have hb := ordinary_rim_correction_bounds hr ψ I γ η hγ hη hn herr
    (fun x D => hzero x x Q.irrefl D)
    (fun x y _ => hbound x y) hspoke
  exact ⟨Φ,ordinary_rim_correction_loads ψ I hload,hb.1,hb.2⟩

end Oberwolfach
