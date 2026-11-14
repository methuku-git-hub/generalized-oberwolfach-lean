module

public import Oberwolfach.MarkedSpokeCorrection

@[expose] public section

/-! Assembly of the marked rim and spoke corrections. The zero residual
row sums are derived from the exact rim equations and graph degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedWheelCorrectionConstant (m : ℕ) (β L C : ℝ) : ℝ :=
  C+markedSpokeCorrectionConstant m β L*(1+(m+1)*C)

theorem marked_wheel_correction {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (β η L δ D C : ℝ) (hβ : 0<β) (hη : 0≤η) (hC : 0≤C)
    (hn : 0<Fintype.card V) (hu : 0<Fintype.card U)
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
    (hinj : Function.Injective (fun e => (tail e,head e)))
    (hkinj : Function.Injective (fun e => (ktail e,khead e)))
    (hK : ∀ v,occurrenceDegree khead v=∑ u,if Hₖ v u then (1:ℝ) else 0)
    (hout : ∀ v,occurrenceDegree (Sum.elim tail ktail) v=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if Hₖ v u then (1:ℝ) else 0))
    (hhub : ∀ u,(∑ v,if H₀ v u then (1:ℝ) else 0)=(m:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0))
    (ψ R : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (hR : ∀ e,markedWheelRimLoad R e=1-markedWheelRimLoad ψ e)
    (hRb : ∀ W,|R W|≤C*η/(Fintype.card V:ℝ)^m)
    (hRsp : ∀ j v u,|markedWheelSpokeLoad R j v u|≤(m+1)*C*η)
    (herr : ∀ j v u,|markedSpokeResidual ψ j v u|≤η) :
    ∃ w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad w e=1) ∧
      (∀ j v u,markedWheelSpokeLoad w j v u=if (if j then Hₖ v u else H₀ v u) then 1 else 0) ∧
      (∀ W,|w W-ψ W|≤markedWheelCorrectionConstant m β L C*η/(Fintype.card V:ℝ)^m) := by
  let ψ₁ := ψ+R
  have hR1 (e : E⊕K) : markedWheelRimLoad ψ₁ e=1 := by
    change markedWheelRimLoad (ψ+R) e=1
    rw [markedWheelRimLoad_add,hR]
    ring
  have hrow : ∀ j v,(∑ u,markedSpokeResidual ψ₁ j v u)=0 :=
    markedSpokeResidual_zero_rows hinj hkinj hK hout ψ₁ hR1
  have hcol : ∀ u,(∑ v,markedSpokeResidual ψ₁ false v u)=(m:ℝ)*(∑ v,markedSpokeResidual ψ₁ true v u) :=
    markedSpokeResidual_column_ratio hhub ψ₁
  let η₁ := (1+(m+1)*C)*η
  have hη₁ : 0≤η₁ := by dsimp [η₁];positivity
  have herr₁ (j : Bool) (v : V) (u : U) : |markedSpokeResidual ψ₁ j v u|≤η₁ := by
    have he : markedSpokeResidual ψ₁ j v u=markedSpokeResidual ψ j v u-markedWheelSpokeLoad R j v u := by
      unfold markedSpokeResidual
      change (if (if j then Hₖ v u else H₀ v u) then 1 else 0)-markedWheelSpokeLoad (ψ+R) j v u=_
      rw [markedWheelSpokeLoad_add]
      ring
    rw [he]
    have hh := abs_sub_le (markedSpokeResidual ψ j v u) 0 (markedWheelSpokeLoad R j v u)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    calc
      _ ≤ η+(m+1)*C*η := hh.trans (add_le_add (herr j v u) (hRsp j v u))
      _ = _ := by dsimp only [η₁];ring
  obtain ⟨S,hSrim,hSspoke,hSb⟩ := marked_spoke_correction β η₁ L δ D hβ hη₁ hn hu p q hdata hsmall
    i hipos hcommon hpaths ψ₁ hrow hcol herr₁
  refine ⟨ψ₁+S,?_,?_,?_⟩
  · intro e
    rw [markedWheelRimLoad_add,hR1,hSrim,add_zero]
  · intro j v u
    rw [markedWheelSpokeLoad_add,hSspoke,markedSpokeResidual]
    ring
  · intro W
    have he : (ψ₁+S) W-ψ W=R W+S W := by dsimp only [ψ₁,Pi.add_apply];ring
    rw [he]
    calc
      _ ≤ |R W|+|S W| := abs_add_le _ _
      _ ≤ C*η/(Fintype.card V:ℝ)^m+markedSpokeCorrectionConstant m β L*η₁/(Fintype.card V:ℝ)^m :=
        add_le_add (hRb W) (hSb W)
      _ = _ := by dsimp only [markedWheelCorrectionConstant,η₁];ring

end Oberwolfach
