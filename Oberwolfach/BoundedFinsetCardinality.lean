module

public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

@[expose] public section

/-! Polynomial bounds for all subsets of bounded size, including the
empty set, by padding their enumerations with absent entries. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A : Type} [Fintype A] [DecidableEq A]

def optionalTupleFinset {h : ℕ} (f : Fin h→Option A) : Finset A :=
  (Finset.univ.image f).eraseNone

theorem optionalTupleFinset_card {h : ℕ} (f : Fin h→Option A) :
    (optionalTupleFinset f).card≤h := by
  unfold optionalTupleFinset
  rw [Finset.card_eraseNone_eq_card_erase]
  exact (Finset.card_erase_le).trans (Finset.card_image_le.trans (by simp))

theorem boundedFinset_optionalTuple (h : ℕ) (S : Finset A) (hS : S.card≤h) :
    ∃ f : Fin h→Option A,optionalTupleFinset f=S := by
  let e := Fintype.equivFin S
  let f : Fin h→Option A := fun i=>if hi : i.val<S.card then
    some (e.symm ⟨i.val,by simpa using hi⟩).val else none
  refine ⟨f,?_⟩
  ext a
  simp only [optionalTupleFinset,Finset.mem_eraseNone,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    dsimp [f] at hi
    split_ifs at hi with h
    · exact Option.some.inj hi ▸ (e.symm ⟨i.val,by simpa using h⟩).property
  · intro ha
    let b : S := ⟨a,ha⟩
    let i : Fin h := ⟨(e b).val,by have hh := (e b).isLt;simp only [Fintype.card_coe] at hh;omega⟩
    refine ⟨i,?_⟩
    have hi : i.val<S.card := by simpa only [i,Fintype.card_coe] using (e b).isLt
    dsimp [f]
    rw [dif_pos hi]
    have hei : (⟨i.val,by simpa using hi⟩ : Fin (Fintype.card S))=e b := by rfl
    rw [hei,e.symm_apply_apply]

theorem boundedFinset_card (h : ℕ) :
    Fintype.card {S : Finset A // S.card≤h}≤(Fintype.card A+1)^h := by
  let f : (Fin h→Option A)→{S : Finset A // S.card≤h} := fun x=>⟨optionalTupleFinset x,optionalTupleFinset_card x⟩
  have hf : Function.Surjective f := by
    intro S
    obtain ⟨x,hx⟩ := boundedFinset_optionalTuple h S.val S.property
    exact ⟨x,Subtype.ext hx⟩
  have hh := Fintype.card_le_of_surjective f hf
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_option] using hh

end Oberwolfach
