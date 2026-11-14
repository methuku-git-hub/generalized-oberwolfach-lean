module

public import Oberwolfach.MarkedCycleRepresentation

@[expose] public section

/-! A marked cycle has a unique canonical sequence. Thus the fixed tuple
family does not duplicate a directed typed cycle under cyclic rotations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedCycleIncidence_ordinary_one_iff {V E K : Type*} [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (C : Fin (m+1) → V)
    (hC : Function.Injective C) (e : E) :
    markedCycleIncidence tail head ktail khead m C (Sum.inl e)=1 ↔
      ∃ j : Fin m,tail e=C j.castSucc ∧ head e=C j.succ := by
  classical
  have hnonneg (j : Fin m) : 0≤directedEdgeIndicator tail head (C j.castSucc) (C j.succ) e := by
    unfold directedEdgeIndicator
    split_ifs <;> norm_num
  constructor
  · intro h
    have hp : 0<∑ j : Fin m,directedEdgeIndicator tail head (C j.castSucc) (C j.succ) e := by
      change 0<markedCycleIncidence tail head ktail khead m C (Sum.inl e)
      rw [h];norm_num
    obtain ⟨j,_,hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => hnonneg j)).mp hp
    refine ⟨j,?_⟩
    by_contra hn
    simp only [directedEdgeIndicator,hn,ite_false] at hj
    exact (lt_irrefl _ hj)
  · rintro ⟨j,hj⟩
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun l : Fin m => directedEdgeIndicator tail head (C l.castSucc) (C l.succ) e)
      (fun l _ => hnonneg l) (Finset.mem_univ j)
    have hid : directedEdgeIndicator tail head (C j.castSucc) (C j.succ) e=1 := by
      simp only [directedEdgeIndicator,hj.1,hj.2,and_self,ite_true]
    rw [hid] at hh
    change 1≤markedCycleIncidence tail head ktail khead m C (Sum.inl e) at hh
    rcases markedCycleIncidence_zero_one tail head ktail khead m C hC (Sum.inl e) with hz | ho
    · rw [hz] at hh;norm_num at hh
    · exact ho

theorem markedCycleIncidence_marked_one_iff {V E K : Type*} [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (C : Fin (m+1) → V) (e : K) :
    markedCycleIncidence tail head ktail khead m C (Sum.inr e)=1 ↔
      ktail e=C (Fin.last m) ∧ khead e=C 0 := by
  simp only [markedCycleIncidence,Sum.elim_inr,directedEdgeIndicator]
  split_ifs <;> simp_all

set_option maxHeartbeats 1000000 in
theorem markedCycleIncidence_injective {V E K : Type*} [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ) :
    Function.Injective (fun C : MarkedCycleTuple tail head ktail khead m π b =>
      markedCycleIncidence tail head ktail khead m C.val) := by
  intro C C' heq
  change markedCycleIncidence tail head ktail khead m C.val=markedCycleIncidence tail head ktail khead m C'.val at heq
  have hC := permutationSeparated_injective π b C.val C.property.1
  have hC' := permutationSeparated_injective π b C'.val C'.property.1
  obtain ⟨e,he⟩ := C.property.2.2
  have hK := (markedCycleIncidence_marked_one_iff tail head ktail khead m C.val e).mpr he
  have hK' : markedCycleIncidence tail head ktail khead m C'.val (Sum.inr e)=1 := by
    rw [← heq];exact hK
  have hz : C.val 0=C'.val 0 := he.2.symm.trans
    ((markedCycleIncidence_marked_one_iff tail head ktail khead m C'.val e).mp hK').2
  have hall : ∀ j : ℕ,∀ hj : j≤m,C.val ⟨j,by omega⟩=C'.val ⟨j,by omega⟩ := by
    intro j
    induction j with
    | zero => intro hj;exact hz
    | succ j ih =>
      intro hj
      let s : Fin m := ⟨j,by omega⟩
      have hprev : C.val s.castSucc=C'.val s.castSucc := ih (by omega)
      obtain ⟨f,hf⟩ := C.property.2.1 s
      have hI := (markedCycleIncidence_ordinary_one_iff tail head ktail khead m C.val hC f).mpr ⟨s,hf⟩
      have hI' : markedCycleIncidence tail head ktail khead m C'.val (Sum.inl f)=1 := by
        rw [← heq];exact hI
      obtain ⟨l,hl⟩ := (markedCycleIncidence_ordinary_one_iff tail head ktail khead m C'.val hC' f).mp hI'
      have hls : l=s := Fin.castSucc_injective m (hC' (hl.1.symm.trans (hf.1.trans hprev)))
      subst l
      exact hf.2.symm.trans hl.2
  apply Subtype.ext
  funext i
  exact hall i.val (by omega)

end Oberwolfach
