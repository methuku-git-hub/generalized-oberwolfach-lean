module

public import Oberwolfach.MarkedSampleOccurrenceMatrix
public import Oberwolfach.MarkedRestrictedDegreeCounts

@[expose] public section

/-! Exact identification of the sampled directed degrees into a fixed set
with the degrees of the corresponding restricted occurrence types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

theorem markedSampleArc_predicate_multiplicity
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (σ : Sym2 V→Option (Bool×Bool)) (mark : Bool) (Q : V→V→Prop) :
    occurrenceMultiplicity
      (fun e:{e:MarkedSampleArc P π b σ mark // Q e.val.1 e.val.2}=>e.val.val.1)
      (fun e=>e.val.val.2)=
    (fun x y=>if Q x y then markedPhysicalRim P π b σ mark x y else 0) := by
  rw [occurrenceMultiplicity_eq_relation _ _ (by
    intro a c he;apply Subtype.ext;exact Subtype.ext he)]
  funext x y
  have he : (∃ e:{e:MarkedSampleArc P π b σ mark // Q e.val.1 e.val.2},
      e.val.val.1=x∧e.val.val.2=y) ↔ markedPhysicalRim P π b σ mark x y=1∧Q x y := by
    constructor
    · rintro ⟨e,hx,hy⟩
      exact ⟨by simpa only [hx,hy] using e.val.property,by simpa only [hx,hy] using e.property⟩
    · rintro ⟨h,hq⟩
      exact ⟨⟨⟨(x,y),h⟩,hq⟩,rfl,rfl⟩
  simp only [relationMultiplicity,he]
  by_cases hq : Q x y
  · simp only [hq,and_true,ite_true,markedPhysicalRim_indicator]
  · simp only [hq,and_false,ite_false]

theorem markedSampleArc_opposite_domain_degrees
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (σ : Sym2 V→Option (Bool×Bool)) (mark : Bool) (x : V) (A : Finset V) :
    let E := {e:MarkedSampleArc P π b σ mark // (if e.val.1=x then e.val.2 else e.val.1)∈A};
    occurrenceDegree (fun e:E=>e.val.val.1) x=(markedRestrictedDegree P π b σ mark false x A:ℝ) ∧
    occurrenceDegree (fun e:E=>e.val.val.2) x=(markedRestrictedDegree P π b σ mark true x A:ℝ) := by
  intro E
  have he := markedSampleArc_predicate_multiplicity P π b σ mark
    (fun u v=>(if u=x then v else u)∈A)
  have he' : occurrenceMultiplicity (fun e:E=>e.val.val.1) (fun e=>e.val.val.2)=
      (fun u v=>if (if u=x then v else u)∈A then markedPhysicalRim P π b σ mark u v else 0) := by
    convert he using 1 <;> congr!
  constructor
  · rw [←occurrenceMultiplicity_row (fun e:E=>e.val.val.1) (fun e=>e.val.val.2),he']
    simp only [ite_true,markedRestrictedDegree,Bool.false_eq_true,ite_false,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
    rw [←Finset.sum_filter]
    simp only [Finset.filter_univ_mem]
  · rw [←occurrenceMultiplicity_col (fun e:E=>e.val.val.1) (fun e=>e.val.val.2),he']
    have hif (y:V) : (if y=x then x else y)=y := by split_ifs with hy;exact hy.symm;rfl
    simp only [hif,markedRestrictedDegree,ite_true,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]
    rw [←Finset.sum_filter]
    simp only [Finset.filter_univ_mem]

end Oberwolfach
