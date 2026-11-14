module

public import Oberwolfach.PairedAbsorberTemplate
public import Oberwolfach.AbsorberFreeCounts

@[expose] public section

/-! Convert every paired realization, with all its ordered labels and
cycle identifiers, to the explicit template. The conversion is injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    {c : ℕ} [NeZero c]

abbrev PairedCycleRecord (R : C → Finset V) (X : Finset V) :=
  Σ f : RootedLabelMap V (c*c) c X,
    {C₀ : C // R C₀=(pairedBasePositions (c:=c)).image f.val} ×
    (∀ i : Fin c,{C₀ : C // R C₀=(pairedZeroPositions i).image f.val}) ×
    (∀ i : Fin c,{C₀ : C // R C₀=(pairedOnePositions i).image f.val})

def pairedCycleRecordToLabelled (R : C → Finset V) (X : Finset V)
    (D : PairedCycleRecord (c:=c) R X) : LabelledCycleRecord R (pairedAbsorberTemplate c).val X := by
  refine ⟨D.1,?_⟩
  intro o
  rcases o with i | j
  · exact D.2.2.1 i
  · refine Fin.cases ?_ (fun i => ?_) j
    · exact D.2.1
    · exact D.2.2.2 i

theorem pairedCycleRecordToLabelled_map (R : C → Finset V) (X : Finset V)
    (D : PairedCycleRecord (c:=c) R X) : (pairedCycleRecordToLabelled R X D).1=D.1 := rfl

theorem pairedCycleRecordToLabelled_base (R : C → Finset V) (X : Finset V)
    (D : PairedCycleRecord (c:=c) R X) :
    ((pairedCycleRecordToLabelled R X D).2 (Sum.inr 0)).val=D.2.1.val := rfl

theorem pairedCycleRecordToLabelled_zero (R : C → Finset V) (X : Finset V)
    (D : PairedCycleRecord (c:=c) R X) (i : Fin c) :
    ((pairedCycleRecordToLabelled R X D).2 (Sum.inl i)).val=(D.2.2.1 i).val := rfl

theorem pairedCycleRecordToLabelled_one (R : C → Finset V) (X : Finset V)
    (D : PairedCycleRecord (c:=c) R X) (i : Fin c) :
    ((pairedCycleRecordToLabelled R X D).2 (Sum.inr i.succ)).val=(D.2.2.2 i).val := rfl

theorem pairedCycleRecordToLabelled_injective (R : C → Finset V) (X : Finset V) :
    Function.Injective (pairedCycleRecordToLabelled (c:=c) R X) := by
  intro D E he
  have hf : D.1=E.1 := congrArg (fun F : LabelledCycleRecord R (pairedAbsorberTemplate c).val X => F.1) he
  have hbase : D.2.1.val=E.2.1.val :=
    congrArg (fun F : LabelledCycleRecord R (pairedAbsorberTemplate c).val X => (F.2 (Sum.inr 0)).val) he
  have hz (i : Fin c) : (D.2.2.1 i).val=(E.2.2.1 i).val :=
    congrArg (fun F : LabelledCycleRecord R (pairedAbsorberTemplate c).val X => (F.2 (Sum.inl i)).val) he
  have ho (i : Fin c) : (D.2.2.2 i).val=(E.2.2.2 i).val :=
    congrArg (fun F : LabelledCycleRecord R (pairedAbsorberTemplate c).val X => (F.2 (Sum.inr i.succ)).val) he
  rcases D with ⟨f,d₀,dz,do'⟩
  rcases E with ⟨g,e₀,ez,eo⟩
  change f=g at hf
  subst g
  have hb : d₀=e₀ := Subtype.ext hbase
  have hzz : dz=ez := funext (fun i => Subtype.ext (hz i))
  have hoo : do'=eo := funext (fun i => Subtype.ext (ho i))
  subst e₀;subst ez;subst eo;rfl

theorem paired_absorber_template_count (R : C → Finset V) (X : Finset V) :
    Fintype.card (PairedCycleRecord (c:=c) R X) ≤
      Fintype.card (LabelledCycleRecord R (pairedAbsorberTemplate c).val X) :=
  Fintype.card_le_of_injective _ (pairedCycleRecordToLabelled_injective R X)

end Oberwolfach
