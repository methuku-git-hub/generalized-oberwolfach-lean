module

public import Oberwolfach.MarkedReplacementTransferBounds
public import Oberwolfach.MarkedWheelCombinations

@[expose] public section

/-! Summing the actual four-wheel gadgets using an edgewise absolute
coefficient load, without multiplying by the number of rectangles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_alternating_correction {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (i : Fin (m+1)) (k : Bool) (hik : markedPositionType i=k)
    (β M : ℝ) (hβ : 0<β) (hM : 0≤M) (hn : 0<Fintype.card V)
    (hcount : ∀ Q : BipartiteFourCycle (if k then Hₖ else H₀),
      β*(Fintype.card V:ℝ)^m≤
      (Fintype.card (MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ))
    (r : V×U → ℝ) (a : BipartiteFourCycle (if k then Hₖ else H₀) → ℝ)
    (hrep : ∀ e,r e=∑ Q,a Q*bipartiteFourCycleVector Q e)
    (hload : ∀ e,(∑ Q,if FourCycleIncident Q e then |a Q| else 0)≤M) :
    ∃ Φ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad Φ e=0) ∧
      (∀ j v u,markedWheelSpokeLoad Φ j v u=if k=j then r (v,u) else 0) ∧
      (∀ D,|Φ D|≤4*M/(β*(Fintype.card V:ℝ)^m)) := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  let T (Q : BipartiteFourCycle (if k then Hₖ else H₀)) :=
    markedReplacementTransfer (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) i Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2
  have hcard (Q : BipartiteFourCycle (if k then Hₖ else H₀)) :
      0<Fintype.card (MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2) := by
    have hh : (0:ℝ)<β*(Fintype.card V:ℝ)^m := by positivity
    exact_mod_cast hh.trans_le (hcount Q)
  have hspoke (Q : BipartiteFourCycle (if k then Hₖ else H₀)) (j : Bool) (v : V) (u : U) :
      markedWheelSpokeLoad (T Q) j v u=if k=j then bipartiteFourCycleVector Q (v,u) else 0 := by
    rw [markedReplacementTransfer_spoke i _ _ _ _ (hcard Q),hik]
    rfl
  let Φ (D : MarkedWheel tail head ktail khead m π b H₀ Hₖ) := ∑ Q,a Q*T Q D
  refine ⟨Φ,?_,?_,?_⟩
  · intro e
    unfold Φ
    rw [markedWheelRimLoad_combination]
    simp only [T,markedReplacementTransfer_rim,mul_zero,Finset.sum_const_zero]
  · intro j v u
    unfold Φ
    rw [markedWheelSpokeLoad_combination]
    simp only [hspoke,mul_ite,mul_zero,Finset.sum_ite_irrel,Finset.sum_const_zero]
    rw [← hrep (v,u)]
  · intro D
    let B := 4/(β*(Fintype.card V:ℝ)^m)
    have hB : 0≤B := by dsimp [B];positivity
    have hsum (Q : BipartiteFourCycle (if k then Hₖ else H₀)) :
        |a Q*T Q D|≤B*(if FourCycleIncident Q (D.1.val i,D.2.val) then |a Q| else 0) := by
      by_cases hi : FourCycleIncident Q (D.1.val i,D.2.val)
      · rw [if_pos hi,abs_mul]
        calc
          _ ≤ |a Q| *B := mul_le_mul_of_nonneg_left
            (markedReplacementTransfer_card_bound i _ _ _ _ β hβ hn (hcount Q) D) (abs_nonneg _)
          _ = _ := by ring
      · have ht : T Q D=0 := markedReplacementTransfer_support i _ _ _ _ D hi
        rw [if_neg hi,ht,mul_zero,abs_zero,mul_zero]
    calc
      _ ≤ ∑ Q,|a Q*T Q D| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ Q,B*(if FourCycleIncident Q (D.1.val i,D.2.val) then |a Q| else 0) :=
        Finset.sum_le_sum (fun Q _=>hsum Q)
      _ = B*(∑ Q,if FourCycleIncident Q (D.1.val i,D.2.val) then |a Q| else 0) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ B*M := mul_le_mul_of_nonneg_left (hload _) hB
      _ = _ := by dsimp only [B];ring

end Oberwolfach
