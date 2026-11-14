module

public import Oberwolfach.MarkedSampleArcs
public import Oberwolfach.OccurrenceRelationMultiplicity

@[expose] public section

/-! The sampled typed arc identifiers have exactly the physical sample's
zero-one adjacency matrix, so degree and cut bounds refer to the same host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem markedSampleArc_indicator_iff (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (σ:Sym2 V→Option (Bool×Bool)) (mark:Bool) (x y:V):
    (∃ e:MarkedSampleArc P π b σ mark,e.val.1=x∧e.val.2=y)↔markedPhysicalRim P π b σ mark x y=1:=by
  constructor
  · rintro ⟨e,hx,hy⟩
    simpa only [hx,hy] using e.property
  · intro h;exact ⟨⟨(x,y),h⟩,rfl,rfl⟩

theorem markedPhysicalRim_indicator (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (σ:Sym2 V→Option (Bool×Bool)) (mark:Bool) (x y:V):
    (if markedPhysicalRim P π b σ mark x y=1 then 1 else 0:ℕ)=markedPhysicalRim P π b σ mark x y:=by
  unfold markedPhysicalRim permutationSeparatedMatrix markedPhysicalOrientation
  split_ifs <;> simp_all

theorem markedSampleArc_multiplicity (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (σ:Sym2 V→Option (Bool×Bool)) (mark:Bool):
    occurrenceMultiplicity (fun e:MarkedSampleArc P π b σ mark=>e.val.1) (fun e=>e.val.2)=
      markedPhysicalRim P π b σ mark:=by
  rw [occurrenceMultiplicity_eq_relation _ _ (fun _ _ he=>Subtype.ext he)]
  funext x y
  simp only [relationMultiplicity,markedSampleArc_indicator_iff,markedPhysicalRim_indicator]

theorem markedSampleArc_degrees (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (σ:Sym2 V→Option (Bool×Bool)) (mark:Bool) (x:V):
    occurrenceDegree (fun e:MarkedSampleArc P π b σ mark=>e.val.1) x=
      ((∑ y,markedPhysicalRim P π b σ mark x y:ℕ):ℝ)∧
    occurrenceDegree (fun e:MarkedSampleArc P π b σ mark=>e.val.2) x=
      ((∑ y,markedPhysicalRim P π b σ mark y x:ℕ):ℝ):=by
  have he:=markedSampleArc_multiplicity P π b σ mark
  constructor
  · rw [Nat.cast_sum]
    exact (occurrenceMultiplicity_row (fun e:MarkedSampleArc P π b σ mark=>e.val.1) (fun e=>e.val.2) x).symm.trans
      (congrArg (fun M:V→V→ℕ=>∑ y,(M x y:ℝ)) he)
  · rw [Nat.cast_sum]
    exact (occurrenceMultiplicity_col (fun e:MarkedSampleArc P π b σ mark=>e.val.1) (fun e=>e.val.2) x).symm.trans
      (congrArg (fun M:V→V→ℕ=>∑ y,(M y x:ℝ)) he)

end Oberwolfach
