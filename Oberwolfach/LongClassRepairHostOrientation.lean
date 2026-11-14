module

public import Oberwolfach.LongClassInnerRequiredRepair
public import Oberwolfach.LongEveryClassSameDeletionReady

@[expose] public section
/-! Every edge added by the class-restricted repair lies in that class and
therefore has an orientation in the actual class witness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem long_class_required_repair_le_class
    (S Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (D:V→V→Prop) (Pack:Finset (Sym2 V)):
    longClassInnerRequiredRepair S Used
      (longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)) I Pack≤S:=by
  intro x y h
  change (spanningRestriction ((S\Used)\Sel) I ⊔ longCloseRequiredGraph S π d D (fun x y=>Used.Adj x y) ⊔
    spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))) I).Adj x y at h
  rcases h with (ha|hb)|hc
  · exact ((spanningRestriction_adj _ _ _ _).mp ha).1.1.1
  · exact hb.1
  · exact ((spanningRestriction_adj _ _ _ _).mp hc).1.1.1

theorem long_class_required_repair_oriented
    (S Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (D:V→V→Prop) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0):
    ∀Pack:Finset (Sym2 V),∀x y,
      (longClassInnerRequiredRepair S Used
        (longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)) I Pack).Adj x y→
      M x y=1∨M y x=1:=by
  intro Pack x y h
  have hs:=long_class_required_repair_le_class S Sel Used π d I D Pack h
  have hh:=hphysical x y
  rw [if_pos hs] at hh
  omega
end Oberwolfach
