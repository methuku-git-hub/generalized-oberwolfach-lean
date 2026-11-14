module

public import Oberwolfach.MixedGreedySequences

@[expose] public section

/-! Actual parent-graph base cycles with one marked head. The last physical
edge joins the last ordinary label to the successor of the marked head.
The greedy count uses ambient-root degree bounds in both spoke classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedBaseRequests {V : Type*} [DecidableEq V] (π : Equiv.Perm V) (m n : ℕ)
    (f : Fin n→V) : Finset V :=
  if h : n=0 then ∅ else
    {f ⟨n-1,by omega⟩} ∪ if n=m then {π (f ⟨0,by omega⟩)} else ∅

theorem markedBaseRequests_card {V : Type*} [DecidableEq V]
    (π : Equiv.Perm V) (m n : ℕ) (f : Fin n→V) : (markedBaseRequests π m n f).card≤2 := by
  unfold markedBaseRequests
  split_ifs
  · simp
  · exact (Finset.card_union_le _ _).trans (by simp)
  · simp

theorem markedBaseRequests_previous {V : Type*} [DecidableEq V]
    (π : Equiv.Perm V) (m n : ℕ) (hn : 0<n) (f : Fin n→V) :
    f ⟨n-1,by omega⟩∈markedBaseRequests π m n f := by
  unfold markedBaseRequests
  rw [dif_neg (by omega)]
  exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

theorem markedBaseRequests_closing {V : Type*} [DecidableEq V]
    (π : Equiv.Perm V) (m : ℕ) (hm : 0<m) (f : Fin m→V) :
    π (f ⟨0,hm⟩)∈markedBaseRequests π m m f := by
  unfold markedBaseRequests
  rw [dif_neg (by omega),if_pos rfl]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

def DenseMarkedBase {V : Type*} (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (T₀ TK : Finset V) {m : ℕ} (f : Fin (m+1)→V) : Prop :=
  PermutationSeparated π b f ∧ f 0∈TK ∧ (∀ i : Fin m,f i.succ∈T₀) ∧
  (∀ i : Fin m,P.Adj (f i.castSucc) (f i.succ)) ∧ P.Adj (f (Fin.last m)) (π (f 0))

theorem mixedGreedyGood_marked_base {V : Type*} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ) (hm : 0<m)
    (T₀ TK : Finset V) (f : Fin (m+1)→V)
    (hf : MixedGreedyGood P π b (fun n=>if n=0 then TK else T₀)
      (fun _=>Equiv.refl V) (markedBaseRequests π m) ∅ f) : DenseMarkedBase P π b T₀ TK f := by
  refine ⟨hf.2.1,?_,?_,?_,?_⟩
  · simpa using hf.1 0
  · intro i
    simpa only [Fin.val_succ,Nat.succ_ne_zero,↓reduceIte] using hf.1 i.succ
  · intro i
    have hp := markedBaseRequests_previous π m (i.val+1) (by omega) (greedyPrefix f i.succ)
    have he : greedyPrefix f i.succ ⟨(i.val+1)-1,by simp only [Fin.val_succ];omega⟩=f i.castSucc := by
      unfold greedyPrefix
      congr 1
    rw [he] at hp
    exact hf.2.2.2 i.succ (f i.castSucc) hp
  · have hp := markedBaseRequests_closing π m hm (greedyPrefix f (Fin.last m))
    have he : greedyPrefix f (Fin.last m) ⟨0,hm⟩=f 0 := by
      unfold greedyPrefix
      congr 1
    rw [he] at hp
    exact (hf.2.2.2 (Fin.last m) (π (f 0)) hp).symm

theorem dense_marked_base_cycle_count {V : Type*} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ) (hm : 0<m)
    (T₀ TK : Finset V) (α a : ℝ) (hα : 0≤α) (hα1 : α≤1) (ha : 0≤a)
    (hbudget : a≤α*min (T₀.card:ℝ) TK.card-((m:ℝ)+1)*(2*(b:ℝ)+1))
    (hdeg₀ : ∀ x : V,(1/2+α/2)*T₀.card≤((P.neighborFinset x∩T₀).card:ℝ))
    (hdegK : ∀ x : V,(1/2+α/2)*TK.card≤((P.neighborFinset x∩TK).card:ℝ)) :
    a^(m+1)≤(Fintype.card {f : Fin (m+1)→V // DenseMarkedBase P π b T₀ TK f}:ℝ) := by
  let A := fun n : ℕ=>if n=0 then TK else T₀
  have hh := mixed_greedy_sequence_count P π b A (fun _=>Equiv.refl V) (markedBaseRequests π m)
    ∅ (m+1) α a hα1 ha (by
      intro n _
      have hcard : min (T₀.card:ℝ) TK.card≤(A n).card := by
        dsimp [A];split_ifs
        · exact min_le_right _ _
        · exact min_le_left _ _
      have hh := mul_le_mul_of_nonneg_left hcard hα
      simp only [Finset.card_empty,Nat.cast_zero,zero_add,Nat.cast_add,Nat.cast_one]
      linarith only [hbudget,hh]) (by
      intro n _ x
      have him : (A n).image (Equiv.refl V)=A n := by simp
      rw [him]
      dsimp [A];split_ifs
      · exact hdegK x
      · exact hdeg₀ x) (by intro n _ f _;exact markedBaseRequests_card π m n f)
  let inj : {f : Fin (m+1)→V // MixedGreedyGood P π b A (fun _=>Equiv.refl V) (markedBaseRequests π m) ∅ f}→
      {f : Fin (m+1)→V // DenseMarkedBase P π b T₀ TK f} :=
    fun f=>⟨f.val,mixedGreedyGood_marked_base P π b m hm T₀ TK f.val f.property⟩
  have hi : Function.Injective inj := by
    intro x y he
    apply Subtype.ext
    exact congrArg (fun z : {f : Fin (m+1)→V // DenseMarkedBase P π b T₀ TK f}=>z.val) he
  exact hh.trans (by exact_mod_cast Fintype.card_le_of_injective inj hi)

theorem denseMarkedBase_physical_injective {V : Type*}
    (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ) (hb : 1≤b) (hm : 2≤m)
    (T₀ TK : Finset V) (f : Fin (m+1)→V) (hf : DenseMarkedBase P π b T₀ TK f) :
    Function.Injective (twistedTupleEdge f (π (f 0))) :=
  separated_successor_edges_injective hm π b hb f hf.1

end Oberwolfach
