module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Image
public import Mathlib.Tactic

@[expose] public section

/-! Counting labelled embeddings with fixed root images. The unrestricted
positions, root positions and positions of a specified cycle remain separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {h c : ℕ}

abbrev RootedLabelMap (V : Type*) [DecidableEq V] (h c : ℕ) (X : Finset V) :=
  {f : Fin h ⊕ Fin c → V // Function.Injective f ∧ Finset.univ.image (fun i => f (Sum.inr i))=X}

def freeLabelPositions (S : Finset (Fin h ⊕ Fin c)) : Finset (Fin h) :=
  Finset.univ.filter (fun i => Sum.inl i∈S)

theorem rootedLabelMap_root_mem (X : Finset V) (f : RootedLabelMap V h c X) (i : Fin c) :
    f.val (Sum.inr i)∈X := by
  have hh : f.val (Sum.inr i)∈Finset.univ.image (fun i => f.val (Sum.inr i)) :=
    Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  simpa only [f.property.2] using hh

theorem rooted_label_maps_constrained_count (X Y : Finset V) (S : Finset (Fin h ⊕ Fin c)) :
    Fintype.card {f : RootedLabelMap V h c X // ∀ j∈S,f.val j∈Y} ≤
      X.card^c*Y.card^(freeLabelPositions S).card*
        Fintype.card V^(h-(freeLabelPositions S).card) := by
  let A := {f : RootedLabelMap V h c X // ∀ j∈S,f.val j∈Y}
  let P := freeLabelPositions S
  let enc (f : A) : (Fin c → X) × (P → Y) × ({j : Fin h // j∉P} → V) :=
    (fun i => ⟨f.val.val (Sum.inr i),rootedLabelMap_root_mem X f.val i⟩,
     fun j => ⟨f.val.val (Sum.inl j.val),f.property _ (Finset.mem_filter.mp j.property).2⟩,
     fun j => f.val.val (Sum.inl j.val))
  have hinj : Function.Injective enc := by
    intro f g he
    apply Subtype.ext
    apply Subtype.ext
    funext j
    rcases j with j | j
    · by_cases hj : j∈P
      · exact congrArg (fun z : Y => z.val) (congrFun (congrArg (fun z => z.2.1) he) ⟨j,hj⟩)
      · exact congrFun (congrArg (fun z => z.2.2) he) ⟨j,hj⟩
    · exact congrArg (fun z : X => z.val) (congrFun (congrArg Prod.fst he) j)
  have hh := Fintype.card_le_of_injective enc hinj
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,
    Fintype.card_subtype_compl,mul_assoc] using hh

theorem rooted_label_maps_count (X : Finset V) :
    Fintype.card (RootedLabelMap V h c X) ≤ X.card^c*Fintype.card V^h := by
  have hh := rooted_label_maps_constrained_count (h:=h) (c:=c) X Finset.univ ∅
  simpa [freeLabelPositions] using hh

end Oberwolfach
