module

public import Oberwolfach.MarkedSampleOccurrenceMatrix
public import Oberwolfach.MarkedUnchangedInnerSample
public import Oberwolfach.BipartiteLargeCutEmbedding

@[expose] public section

/-! The actual occurrence matrices on an induced row set are the
restrictions of the original matrices. An empty physical deletion on an
invariant inner pair therefore preserves its matrices and cut bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem occurrenceMultiplicity_induced
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
    (tail head : E→V) (hinj : Function.Injective (fun e=>(tail e,head e))) (I : Finset V) :
    occurrenceMultiplicity
      (fun e:{e:E // tail e∈I∧head e∈I}=>(⟨tail e.val,e.property.1⟩:I))
      (fun e=>(⟨head e.val,e.property.2⟩:I))=
      (fun x:I=>fun y:I=>occurrenceMultiplicity tail head x.val y.val) := by
  let t := fun e:{e:E // tail e∈I∧head e∈I}=>(⟨tail e.val,e.property.1⟩:I)
  let h := fun e:{e:E // tail e∈I∧head e∈I}=>(⟨head e.val,e.property.2⟩:I)
  have hi : Function.Injective (fun e=>(t e,h e)) := by
    intro a b he
    apply Subtype.ext
    apply hinj
    exact Prod.ext (congrArg (fun z:I×I=>z.1.val) he) (congrArg (fun z:I×I=>z.2.val) he)
  rw [occurrenceMultiplicity_eq_relation _ _ hi,occurrenceMultiplicity_eq_relation tail head hinj]
  funext x y
  unfold relationMultiplicity
  congr 1
  apply propext
  constructor
  · rintro ⟨e,he,hf⟩
    exact ⟨e.val,congrArg Subtype.val he,congrArg Subtype.val hf⟩
  · rintro ⟨e,he,hf⟩
    exact ⟨⟨e,he ▸ x.property,hf ▸ y.property⟩,Subtype.ext he,Subtype.ext hf⟩

theorem markedSampleArc_induced_multiplicity
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (σ : Sym2 V→Option (Bool×Bool)) (mark : Bool) (I : Finset V) :
    occurrenceMultiplicity
      (fun e:{e:MarkedSampleArc P π b σ mark // e.val.1∈I∧e.val.2∈I}=>(⟨e.val.val.1,e.property.1⟩:I))
      (fun e=>(⟨e.val.val.2,e.property.2⟩:I))=
      (fun x:I=>fun y:I=>markedPhysicalRim P π b σ mark x.val y.val) := by
  rw [occurrenceMultiplicity_induced _ _ (fun _ _ h=>Subtype.ext h),markedSampleArc_multiplicity]

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_induced_rim_matrix_unchanged
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (I : Finset V) (hI : ∀ x,π x∈I↔x∈I) (DR : SimpleGraph V)
    (hDR : ∀ x∈I,∀ y∈I,¬DR.Adj x y) (mark : Bool) :
    (fun x:I=>fun y:I=>markedPhysicalRim P π (3*d)
      (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x.val y.val)=
    (fun x:I=>fun y:I=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x.val y.val) := by
  funext x y
  have hn : s(x.val,if mark then π y.val else y.val)∉DR.edgeFinset := by
    intro h
    have hy : (if mark then π y.val else y.val)∈I := by
      cases mark with
      | false => exact y.property
      | true => exact (hI y.val).mpr y.property
    exact hDR x.val x.property _ hy (SimpleGraph.mem_edgeFinset.mp h)
  have he : (markedPhysicalRim P π (3*d)
      (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x.val y.val=1) ↔
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x.val y.val=1 := by
    simpa only [hn,not_false_eq_true,and_true] using markedPhysicalRim_delete_iff P π d σ DR.edgeFinset mark x.val y.val
  calc
    _ = (if markedPhysicalRim P π (3*d)
        (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x.val y.val=1 then 1 else 0:ℕ) :=
      (markedPhysicalRim_indicator P π (3*d) _ mark x.val y.val).symm
    _ = (if markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x.val y.val=1 then 1 else 0:ℕ) := by simp only [he]
    _ = _ := markedPhysicalRim_indicator P π (3*d) _ mark x.val y.val

theorem marked_induced_occurrence_cuts_unchanged
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (I : Finset V) (hI : ∀ x,π x∈I↔x∈I) (DR : SimpleGraph V)
    (hDR : ∀ x∈I,∀ y∈I,¬DR.Adj x y) (δ h : ℝ) (mark : Bool) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) mark
    let E' := MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark;
    BipartiteLargeCut (occurrenceMultiplicity
      (fun e:{e:E // e.val.1∈I∧e.val.2∈I}=>(⟨e.val.val.1,e.property.1⟩:I))
      (fun e=>(⟨e.val.val.2,e.property.2⟩:I))) δ h ↔
    BipartiteLargeCut (occurrenceMultiplicity
      (fun e:{e:E' // e.val.1∈I∧e.val.2∈I}=>(⟨e.val.val.1,e.property.1⟩:I))
      (fun e=>(⟨e.val.val.2,e.property.2⟩:I))) δ h := by
  intro E E'
  rw [markedSampleArc_induced_multiplicity,markedSampleArc_induced_multiplicity,
    marked_induced_rim_matrix_unchanged P π d σ I hI DR hDR mark]

end Oberwolfach
