module

public import Oberwolfach.MarkedReplacementTransfers

@[expose] public section

/-! A fixed wheel can occur only in rectangles containing its spoke at
the replacement position. This is the support needed for incident loads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}

theorem markedReplacementTransfer_support (i : Fin (m+1)) (v v' : V) (u u' : U)
    (D : MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hout : ¬((D.1.val i=v ∨ D.1.val i=v') ∧ (D.2.val=u ∨ D.2.val=u'))) :
    markedReplacementTransfer i v v' u u' D=0 := by
  have hnot (a d : Bool) (P : MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u') :
      D≠markedReplacementWheel a d P := by
    intro he
    apply hout
    rw [he]
    cases a <;> cases d <;>
      simp only [markedReplacementWheel,Function.Embedding.coeFn_mk,Bool.false_eq_true,ite_false,ite_true,
        P.property.1,P.property.2.1,true_or,or_true,and_self]
  exact averagedBasisRectangle_zero _ _ _ _ D (hnot false false) (hnot true false)
    (hnot true true) (hnot false true)

theorem markedReplacementTransfer_card_bound (i : Fin (m+1)) (v v' : V) (u u' : U)
    (β : ℝ) (hβ : 0<β) (hn : 0<Fintype.card V)
    (hcount : β*(Fintype.card V:ℝ)^m≤
      (Fintype.card (MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u'):ℝ))
    (D : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    |markedReplacementTransfer i v v' u u' D|≤4/(β*(Fintype.card V:ℝ)^m) := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  exact (markedReplacementTransfer_bound i v v' u u' D).trans
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) hcount)

end Oberwolfach
