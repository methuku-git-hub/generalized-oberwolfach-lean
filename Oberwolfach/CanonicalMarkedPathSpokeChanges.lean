module

public import Oberwolfach.TwoHubTupleChanges

@[expose] public section

/-! Spoke changes in canonical common paths count only the free vertices;
neither fixed root is required to have a spoke. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem canonicalCommonMarkedPath_spoke_changes
    {V U E K:Type*} [Fintype V] [DecidableEq V]
    (tail head:E→V) (ktail khead:K→V) (m:ℕ) (π:Equiv.Perm V) (b:ℕ)
    (H H':Bool→V→U→Prop) (i:Fin (m+1)) (v v':V) (u u':U) (δ:ℝ)
    (hcol:∀ b u,(∑ x,if ¬(H b x u↔H' b x u) then (1:ℝ) else 0)≤δ):
    (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead m π b (H false) (H true) i v v' u u'):ℝ)-
      Fintype.card (CanonicalCommonMarkedPath tail head ktail khead m π b (H' false) (H' true) i v v' u u')≤
      2*(m:ℝ)*δ*(Fintype.card V:ℝ)^(m-1):=by
  let base:=fun z:Fin m→V=>
    IsMarkedCycleTuple tail head ktail khead m π b (Fin.insertNth i v z)∧
    IsMarkedCycleTuple tail head ktail khead m π b (Fin.insertNth i v' z)
  have he (J:Bool→V→U→Prop):
      CanonicalCommonMarkedPath tail head ktail khead m π b (J false) (J true) i v v' u u'≃
      {z:Fin m→V // base z∧∀ a,J (markedPositionType (i.succAbove a)) (z a) u∧
        J (markedPositionType (i.succAbove a)) (z a) u'}:=by
    apply Equiv.subtypeEquivRight
    intro z
    have hs (a:Fin m) (w:U):
        (if markedPositionType (i.succAbove a) then J true (z a) w else J false (z a) w)↔
          J (markedPositionType (i.succAbove a)) (z a) w:=by
      cases markedPositionType (i.succAbove a) <;> simp
    simp only [hs,base,and_assoc]
  rw [Fintype.card_congr (he H),Fintype.card_congr (he H')]
  have hh:=twoHubTuple_spoke_loss H H' u u' (fun a:Fin m=>markedPositionType (i.succAbove a)) base δ hcol
  simp only [Fintype.card_fin] at hh
  simp only [Fintype.card_eq_nat_card] at hh ⊢
  convert hh using 1 <;> ring

end Oberwolfach
