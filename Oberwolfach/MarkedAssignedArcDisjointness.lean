module

public import Oberwolfach.MarkedRowRimClassification
public import Oberwolfach.FiniteLabelConflicts

@[expose] public section

/-! The root-rim disjointness and attachment multiplicity inputs follow
from distinct actual incoming/outgoing arcs and bijective assignments. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K : Type} [DecidableEq V]

theorem markedPhysicalEdge_typed_formula (tail head : E → V) (ktail khead : K → V)
    (π : Equiv.Perm V) (e : E⊕K) :
    markedPhysicalEdge tail head ktail khead π e=
      if e.isRight then {Sum.elim tail ktail e,π (Sum.elim head khead e)}
      else {Sum.elim tail ktail e,Sum.elim head khead e} := by
  cases e <;> rfl

theorem markedArcPresent_of_edge (tail head : E → V) (ktail khead : K → V) (e : E⊕K) :
    markedArcPresent tail head ktail khead e.isRight (Sum.elim tail ktail e) (Sum.elim head khead e) := by
  cases e with
  | inl e => exact ⟨e,rfl,rfl⟩
  | inr e => exact ⟨e,rfl,rfl⟩

theorem marked_assigned_root_rims_disjoint {I : Type}
    (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (v : V) (incoming outgoing : I → E⊕K)
    (hi : Function.Injective incoming) (ho : Function.Injective outgoing)
    (hhead : ∀ i, Sum.elim head khead (incoming i)=v)
    (htail : ∀ i, Sum.elim tail ktail (outgoing i)=v)
    (hloop : ∀ i, Sum.elim tail ktail (incoming i)≠v) :
    ∀ i j, i≠j → Disjoint
      (markedRowRootRims π v (Sum.elim head khead (outgoing i)) (Sum.elim tail ktail (incoming i))
        (incoming i).isRight (outgoing i).isRight)
      (markedRowRootRims π v (Sum.elim head khead (outgoing j)) (Sum.elim tail ktail (incoming j))
        (incoming j).isRight (outgoing j).isRight) := by
  have he (i : I) : markedRowRootRims π v
      (Sum.elim head khead (outgoing i)) (Sum.elim tail ktail (incoming i))
      (incoming i).isRight (outgoing i).isRight=
      {markedPhysicalEdge tail head ktail khead π (outgoing i),markedPhysicalEdge tail head ktail khead π (incoming i)} := by
    simp only [markedRowRootRims,markedPhysicalEdge_typed_formula,hhead,htail]
  have hcross (i j : I) : outgoing i≠incoming j := by
    intro h
    exact hloop j ((congrArg (Sum.elim tail ktail) h).symm.trans (htail i))
  intro i j hij
  rw [he,he]
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have hei' : e=markedPhysicalEdge tail head ktail khead π (outgoing i) ∨
      e=markedPhysicalEdge tail head ktail khead π (incoming i) := by simpa using hei
  have hej' : e=markedPhysicalEdge tail head ktail khead π (outgoing j) ∨
      e=markedPhysicalEdge tail head ktail khead π (incoming j) := by simpa using hej
  rcases hei' with hei|hei <;> rcases hej' with hej|hej
  · exact hij (ho (hp (hei.symm.trans hej)))
  · exact hcross i j (hp (hei.symm.trans hej))
  · exact hcross j i (hp (hej.symm.trans hei))
  · exact hij (hi (hp (hei.symm.trans hej)))

theorem paired_label_occurrence_bound {I A X V : Type*} [Fintype I] [Fintype A] [Fintype X]
    (labelA : A → V) (labelX : X → V) (f : I ≃ A) (g : I ≃ X) (M : ℕ)
    (hA : ∀ v, Fintype.card {a // labelA a=v}≤M)
    (hX : ∀ v, Fintype.card {x // labelX x=v}≤M) :
    ∀ v, (Finset.univ.filter (fun i => v=labelA (f i) ∨ v=labelX (g i))).card≤2*M := by
  intro v
  have h₁ : (Finset.univ.filter (fun i => v=labelA (f i))).card≤M := by
    simpa only [Fintype.card_subtype,eq_comm] using label_fibre_bound_reindex labelA f M hA v
  have h₂ : (Finset.univ.filter (fun i => v=labelX (g i))).card≤M := by
    simpa only [Fintype.card_subtype,eq_comm] using label_fibre_bound_reindex labelX g M hX v
  rw [Finset.filter_or]
  have hh := Finset.card_union_le (Finset.univ.filter (fun i => v=labelA (f i)))
    (Finset.univ.filter (fun i => v=labelX (g i)))
  omega

end Oberwolfach
