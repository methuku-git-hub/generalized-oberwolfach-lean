module

public import Oberwolfach.AdaptiveSelectionProcess

@[expose] public section

/-! Exact changes of the fixed test counters when one unassigned position
is filled. Future choices do not alter an earlier compatibility check. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {I C : Type*} [Fintype I]

def selectionCounter (active : Fin N→I→Prop) (hit : I→C→Prop) (F : Fin N→C) (x : I) : ℕ :=
  (Finset.univ.filter (fun j=>active j x ∧ hit x (F j))).card

theorem selectionCounter_empty (active : Fin N→I→Prop) (hit : I→C→Prop)
    (empty : C) (hempty : ∀ x,¬hit x empty) (x : I) :
    selectionCounter active hit (fun _=>empty) x=0 := by
  simp [selectionCounter,hempty]

theorem selectionCounter_update (active : Fin N→I→Prop) (hit : I→C→Prop)
    (F : Fin N→C) (i : Fin N) (c : C) (x : I) (hbefore : ¬hit x (F i)) :
    selectionCounter active hit (Function.update F i c) x=
      selectionCounter active hit F x+(if active i x ∧ hit x c then 1 else 0) := by
  let S := Finset.univ.filter (fun j=>active j x ∧ hit x (F j))
  have hi : i∉S := by simp [S,hbefore]
  by_cases hnew : active i x ∧ hit x c
  · have he : Finset.univ.filter (fun j=>active j x ∧ hit x (Function.update F i c j))=insert i S := by
      ext j
      by_cases hj : j=i
      · subst j;simp [hnew]
      · simp [Function.update_of_ne hj,S,hj]
    rw [if_pos hnew]
    change _=S.card+1
    simpa only [selectionCounter,he,Finset.card_insert_of_notMem hi]
  · have he : Finset.univ.filter (fun j=>active j x ∧ hit x (Function.update F i c j))=S := by
      ext j
      by_cases hj : j=i
      · subst j;simp [S,hnew,hbefore]
      · simp [Function.update_of_ne hj,S,hj]
    simp only [selectionCounter,he,if_neg hnew,Nat.add_zero]
    rfl

def SelectionPrefix (allowed : Fin N→C→Prop) (compatible : C→C→Prop)
    (empty : C) (k : ℕ) (F : Fin N→C) : Prop :=
  (∀ i,k ≤ i.val → F i=empty) ∧
  (∀ i,i.val < k → allowed i (F i)) ∧
  (∀ i j,i.val < j.val → j.val < k → compatible (F i) (F j))

theorem selectionPrefix_zero (allowed : Fin N→C→Prop) (compatible : C→C→Prop) (empty : C) :
    SelectionPrefix allowed compatible empty 0 (fun _=>empty) := by
  exact ⟨fun _ _=>rfl,fun i hi=>False.elim (by omega),fun i j hij hj=>False.elim (by omega)⟩

theorem selectionPrefix_update (allowed : Fin N→C→Prop) (compatible : C→C→Prop)
    (empty : C) (i : Fin N) (F : Fin N→C) (c : C)
    (hF : SelectionPrefix allowed compatible empty i.val F)
    (hc : allowed i c) (hcomp : ∀ j,j.val < i.val → compatible (F j) c) :
    SelectionPrefix allowed compatible empty (i.val+1) (Function.update F i c) := by
  refine ⟨?_,?_,?_⟩
  · intro j hj
    have hne : j≠i := by intro he;subst j;omega
    rw [Function.update_of_ne hne]
    exact hF.1 j (by omega)
  · intro j hj
    by_cases he : j=i
    · subst j;simpa using hc
    · rw [Function.update_of_ne he]
      have hne : j.val≠i.val := fun hh=>he (Fin.ext hh)
      exact hF.2.1 j (by omega)
  · intro a b hab hb
    have hai : a≠i := by intro he;subst a;omega
    rw [Function.update_of_ne hai]
    by_cases hbi : b=i
    · subst b;simp only [Function.update_self];exact hcomp a hab
    · rw [Function.update_of_ne hbi]
      have hne : b.val≠i.val := fun hh=>hbi (Fin.ext hh)
      exact hF.2.2 a b hab (by omega)

theorem sequential_select_bounded_hits
    {A : Type*} [Fintype A] [Nonempty A]
    (B : ℕ) (active : Fin N→I→Prop) (hit : I→C→Prop)
    (allowed : Fin N→C→Prop) (compatible : C→C→Prop)
    (empty : C) (hempty : ∀ x,¬hit x empty) (q : ℝ) (hq : 0 ≤ q)
    (hsmall : selectionPotential active q 0 (fun _=>0) < (2:ℝ)^B)
    (hchoice : ∀ i : Fin N,∀ F,SelectionPrefix allowed compatible empty i.val F →
      (∀ x,selectionCounter active hit F x < B) →
      ∃ candidates : A→C,
        (∀ a,allowed i (candidates a)) ∧
        (∀ a j,j.val < i.val → compatible (F j) (candidates a)) ∧
        (∀ x,active i x → ((Finset.univ.filter (fun a=>hit x (candidates a))).card:ℝ) ≤ q*Fintype.card A)) :
    ∃ F : Fin N→C,(∀ i,allowed i (F i)) ∧
      (∀ i j,i.val < j.val → compatible (F i) (F j)) ∧
      ∀ x,selectionCounter active hit F x < B := by
  obtain ⟨F,hF,hcount⟩ := adaptive_selection_process N B active q hq
    (selectionCounter active hit) (SelectionPrefix allowed compatible empty) (fun _=>empty)
    (selectionPrefix_zero allowed compatible empty)
    (selectionCounter_empty active hit empty hempty) hsmall (by
      intro i F hprefix hsafe
      obtain ⟨candidates,hallowed,hcompat,hcounts⟩ := hchoice i F hprefix hsafe
      refine ⟨fun a=>Function.update F i (candidates a),fun a x=>active i x ∧ hit x (candidates a),?_,?_,?_,?_⟩
      · exact fun a=>selectionPrefix_update allowed compatible empty i F (candidates a) hprefix (hallowed a) (hcompat a)
      · intro a x
        convert selectionCounter_update active hit F i (candidates a) x (by rw [hprefix.1 i le_rfl];exact hempty x) using 1 <;> congr!
      · intro x hx a;exact fun hh=>hx hh.1
      · intro x
        by_cases hx : active i x
        · simpa only [hx,true_and] using hcounts x hx
        · simp only [hx,false_and,Finset.filter_false,Finset.card_empty,Nat.cast_zero]
          positivity)
  exact ⟨F,fun i=>hF.2.1 i i.isLt,fun i j hij=>hF.2.2 i j hij j.isLt,hcount⟩

end Oberwolfach
