module

public import Oberwolfach.MarkedReplacementPairs
public import Oberwolfach.FiniteBasisRectangles
public import Oberwolfach.SparseAlternatingCorrection

@[expose] public section

/-! Actual four-wheel corrections from pairs of cycles differing at one
position. Both rim cancellation and typed spoke equations are exact. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}

def markedReplacementTransfer (i : Fin (m+1)) (v v' : V) (u u' : U) :
    MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ :=
  averagedBasisRectangle
    (markedReplacementWheel (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) (i:=i) (v:=v) (v':=v') (u:=u) (u':=u') false false)
    (markedReplacementWheel true false) (markedReplacementWheel true true) (markedReplacementWheel false true)

theorem markedReplacementTransfer_rim (i : Fin (m+1)) (v v' : V) (u u' : U) (e : E⊕K) :
    markedWheelRimLoad (markedReplacementTransfer (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) i v v' u u') e=0 := by
  unfold markedWheelRimLoad markedReplacementTransfer
  rw [averagedBasisRectangle_test]
  apply div_eq_zero_iff.mpr
  left
  apply Finset.sum_eq_zero
  intro P _
  change (markedCycleIncidence tail head ktail khead m P.val.1.val e-
    markedCycleIncidence tail head ktail khead m P.val.2.val e+
    markedCycleIncidence tail head ktail khead m P.val.2.val e-
    markedCycleIncidence tail head ktail khead m P.val.1.val e)=0
  ring

theorem markedReplacementTransfer_spoke (i : Fin (m+1)) (v v' : V) (u u' : U)
    (hc : 0<Fintype.card (MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u'))
    (j : Bool) (a : V) (h : U) :
    markedWheelSpokeLoad (markedReplacementTransfer (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) i v v' u u') j a h=
      if markedPositionType i=j then alternatingRectangle v v' u u' a h else 0 := by
  unfold markedWheelSpokeLoad markedReplacementTransfer
  rw [averagedBasisRectangle_test]
  have hpoint (P : MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u') :
      (if u=h then markedSpokeIndicator P.val.1.val j a else 0)-
      (if u=h then markedSpokeIndicator P.val.2.val j a else 0)+
      (if u'=h then markedSpokeIndicator P.val.2.val j a else 0)-
      (if u'=h then markedSpokeIndicator P.val.1.val j a else 0)=
        if markedPositionType i=j then alternatingRectangle v v' u u' a h else 0 := by
    have hd := markedSpokeIndicator_replacement P.val.1.val P.val.2.val i P.property.2.2.1 j a
    rw [P.property.1,P.property.2.1] at hd
    calc
      _ = ((if u=h then (1:ℝ) else 0)-(if u'=h then 1 else 0))*
          (markedSpokeIndicator P.val.1.val j a-markedSpokeIndicator P.val.2.val j a) := by
        split_ifs <;> ring
      _ = _ := by
        have hV (s t : V) : (if s=t then (1:ℝ) else 0)=(if t=s then 1 else 0) := by simp only [eq_comm]
        have hU (s t : U) : (if s=t then (1:ℝ) else 0)=(if t=s then 1 else 0) := by simp only [eq_comm]
        rw [hd,hV v a,hV v' a,hU u h,hU u' h]
        unfold alternatingRectangle
        split_ifs <;> ring
  change (∑ P : MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u',
    ((if u=h then markedSpokeIndicator P.val.1.val j a else 0)-
     (if u=h then markedSpokeIndicator P.val.2.val j a else 0)+
     (if u'=h then markedSpokeIndicator P.val.2.val j a else 0)-
     (if u'=h then markedSpokeIndicator P.val.1.val j a else 0)))/_= _
  simp only [hpoint,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hn : (Fintype.card (MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u'):ℝ)≠0 :=
    (Nat.cast_pos.mpr hc).ne'
  field_simp

theorem markedReplacementTransfer_bound (i : Fin (m+1)) (v v' : V) (u u' : U)
    (D : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    |markedReplacementTransfer i v v' u u' D|≤
      4/(Fintype.card (MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u'):ℝ) :=
  averagedBasisRectangle_bound _ _ _ _ D

end Oberwolfach
