module

public import Oberwolfach.PairedTupleCounts

@[expose] public section

/-! Every disjoint choice of a base cycle and common paths gives the
specified paired absorber, with all labels and cycle identifiers retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] {m : ℕ}

variable (R : C → Finset V) (x : Fin (m+1) → V) (hx : Function.Injective x)
  (Base : (Fin (m+1) → V) → Prop)
  (Path : (Fin (m+1) → V) → ℕ → (Fin m → V) → Prop)
  (hbinj : ∀ y,Base y → Function.Injective y)
  (hb : ∀ y,Base y → ∃ C₀,R C₀=Finset.univ.image y)
  (hpaths : ∀ y,Base y → (∀ i,y i∉Finset.univ.image x) → ∀ i : Fin (m+1),∀ g,Path y i.val g →
    (∃ C₀,R C₀=insert (y i) (Finset.univ.image g)) ∧
    (∃ C₁,R C₁=insert (x i) (Finset.univ.image g)))

def pairedTupleChoiceToRecord (D : PairedTupleChoice x Base Path) :
    PairedCycleRecord (c:=m+1) R (Finset.univ.image x) := by
  let y := D.1.val
  let g := D.2.val
  have hxy (i j : Fin (m+1)) : y i≠x j := by
    intro he
    exact D.1.property.2 i (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he.symm⟩)
  let f : RootedLabelMap V ((m+1)*(m+1)) (m+1) (Finset.univ.image x) :=
    ⟨pairedTupleLabels x y g,pairedTupleLabels_injective x y g hx (hbinj y D.1.property.1)
      hxy D.2.property.2.1 D.2.property.2.2,rfl⟩
  have hp (i : Fin (m+1)) := hpaths y D.1.property.1 D.1.property.2 i (g i) (D.2.property.1 i)
  refine ⟨f,⟨Classical.choose (hb y D.1.property.1),?_⟩,
    (fun i => ⟨Classical.choose (hp i).1,?_⟩),
    (fun i => ⟨Classical.choose (hp i).2,?_⟩)⟩
  · exact (Classical.choose_spec (hb y D.1.property.1)).trans (pairedTupleLabels_base x y g).symm
  · exact (Classical.choose_spec (hp i).1).trans (pairedTupleLabels_zero x y g i).symm
  · exact (Classical.choose_spec (hp i).2).trans (pairedTupleLabels_one x y g i).symm

theorem pairedTupleChoiceToRecord_labels (D : PairedTupleChoice x Base Path) :
    (pairedTupleChoiceToRecord R x hx Base Path hbinj hb hpaths D).1.val=
      pairedTupleLabels x D.1.val D.2.val := rfl

theorem pairedTupleChoiceToRecord_injective :
    Function.Injective (pairedTupleChoiceToRecord R x hx Base Path hbinj hb hpaths) := by
  intro D E he
  have hf := congrArg (fun D : PairedCycleRecord (c:=m+1) R (Finset.univ.image x) => D.1.val) he
  rw [pairedTupleChoiceToRecord_labels,pairedTupleChoiceToRecord_labels] at hf
  rcases D with ⟨⟨y,hy⟩,⟨g,hg⟩⟩
  rcases E with ⟨⟨z,hz⟩,⟨h,hh⟩⟩
  have hyz : y=z := by
    funext i
    have he := congrFun hf (pairedFreePosition i 0)
    simpa only [pairedTupleLabels_free,Fin.cons_zero] using he
  subst z
  have hgh : g=h := by
    funext i j
    have he := congrFun hf (pairedFreePosition i j.succ)
    simpa only [pairedTupleLabels_free,Fin.cons_succ] using he
  subst h
  rfl

include hx hbinj hb hpaths in
theorem paired_absorber_count_from_choices :
    Fintype.card (PairedTupleChoice x Base Path)≤
      Fintype.card (LabelledCycleRecord R (pairedAbsorberTemplate (m+1)).val (Finset.univ.image x)) :=
  (Fintype.card_le_of_injective _
    (pairedTupleChoiceToRecord_injective R x hx Base Path hbinj hb hpaths)).trans
    (paired_absorber_template_count R (Finset.univ.image x))

end Oberwolfach
