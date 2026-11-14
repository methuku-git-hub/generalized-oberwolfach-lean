module

public import Oberwolfach.MarkedRestrictedLoadIdentities
public import Oberwolfach.MarkedSpokeResiduals

@[expose] public section

/-! Restriction of the fixed positive approximate weighting. Surviving wheels
retain their parent weights. Residuals at absent spokes are exactly zero;
the original unit targets are used at each surviving edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m b : ℕ} {π : Equiv.Perm V}
  {H₀ Hₖ H₀' Hₖ' : V → U → Prop}

theorem marked_approximate_weights_restriction
    (hm : 3≤m) (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (Blo B η d : ℝ) (hBlo : 0≤Blo) (hB : 0≤B) (hη : 0≤η) (hd : 0≤d)
    (hw : ∀ W,Blo/(Fintype.card V:ℝ)^m≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (hR : ∀ e,|markedWheelRimLoad w e-1|≤η)
    (hS : ∀ j v u,|markedSpokeResidual w j v u|≤η)
    (hout : ∀ x,(∑ e,if ¬Sum.elim PE PK e ∧ Sum.elim tail ktail e=x then (1:ℝ) else 0)≤d)
    (hin : ∀ x,(∑ e,if ¬Sum.elim PE PK e ∧ Sum.elim head khead e=x then (1:ℝ) else 0)≤d)
    (hHout : ∀ x,(∑ u,bipAdj (fun x u=>(H₀ x u ∨ Hₖ x u) ∧ ¬(H₀' x u ∨ Hₖ' x u)) x u)≤d)
    (hHin : ∀ u,(∑ x,bipAdj (fun x u=>(H₀ x u ∨ Hₖ x u) ∧ ¬(H₀' x u ∨ Hₖ' x u)) x u)≤d) :
    let w' := fun W=>w (markedWheelToLarger PE PK hH₀ hHₖ W)
    (∀ W,Blo/(Fintype.card V:ℝ)^m≤w' W ∧ w' W≤B/(Fintype.card V:ℝ)^m) ∧
    (∀ e,|markedWheelRimLoad w' e-1|≤η+8*((m:ℝ)+1)^4*B*d/Fintype.card V) ∧
    (∀ j v u,|markedSpokeResidual w' j v u|≤η+8*((m:ℝ)+1)^4*B*d/Fintype.card V) := by
  let w' := fun W=>w (markedWheelToLarger PE PK hH₀ hHₖ W)
  have hnn : 0≤(Fintype.card V:ℝ) := by positivity
  have hw0 (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
      0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m :=
    ⟨(by positivity : 0≤Blo/(Fintype.card V:ℝ)^m).trans (hw W).1,(hw W).2⟩
  refine ⟨fun W=>hw _,?_,?_⟩
  · intro e
    have hloss := marked_restricted_rim_load_stability hm hp hn hu PE PK hH₀ hHₖ hdisj
      w B d hB hd hw0 hout hin hHout hHin e
    have hbase := hR (Sum.map Subtype.val Subtype.val e)
    have ht := abs_sub_le (markedWheelRimLoad w' e)
      (markedWheelRimLoad w (Sum.map Subtype.val Subtype.val e)) 1
    change |markedWheelRimLoad w' e-1|≤_
    linarith
  · intro j v u
    by_cases he : if j then Hₖ' v u else H₀' v u
    · have heparent : if j then Hₖ v u else H₀ v u := by
        cases j
        · exact hH₀ v u he
        · exact hHₖ v u he
      have hloss := marked_restricted_spoke_load_stability hm hp hn hu PE PK hH₀ hHₖ hdisj
        w B d hB hd hw0 hout hin hHout hHin j v u he
      have hbase := hS j v u
      simp only [markedSpokeResidual,if_pos heparent] at hbase
      change |markedSpokeResidual w' j v u|≤_
      rw [markedSpokeResidual,if_pos he]
      have ht := abs_sub_le 1 (markedWheelSpokeLoad w j v u) (markedWheelSpokeLoad w' j v u)
      rw [abs_sub_comm (markedWheelSpokeLoad w j v u)] at ht
      have hle : 4*((m:ℝ)+1)^4*B*d/Fintype.card V≤8*((m:ℝ)+1)^4*B*d/Fintype.card V := by
        apply div_le_div_of_nonneg_right _ hnn
        have hnon : 0≤((m:ℝ)+1)^4*B*d := by positivity
        nlinarith
      linarith
    · change |markedSpokeResidual w' j v u|≤_
      rw [markedSpokeResidual_outside w' j v u he,abs_zero]
      positivity

end Oberwolfach
