module

public import Oberwolfach.SeparatedPairWeights
public import Oberwolfach.SuccessorGoodPartitions
public import Oberwolfach.AlternatingCycle

@[expose] public section

/-! The paired coordinates are put into the ordinary cyclic order.
Only the closing interface is twisted; its physical endpoint is π(x₀). -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def pairPositionEquiv (k : ℕ) : (Fin (k+2) ⊕ Fin (k+2)) ≃ Fin ((k+2)*2) where
  toFun s := match s with
    | Sum.inl i => alternatingIndex i 0
    | Sum.inr i => alternatingIndex i 1
  invFun j := let p := finProdFinEquiv.symm j
    if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  left_inv s := by cases s <;> simp [alternatingIndex]
  right_inv j := by
    obtain ⟨⟨i,b⟩,rfl⟩ := finProdFinEquiv.surjective j
    fin_cases b <;> simp [alternatingIndex]

theorem pairPositionEquiv_symm_zero (k : ℕ) (i : Fin (k+2)) :
    (pairPositionEquiv k).symm (alternatingIndex i 0) = Sum.inl i :=
  (pairPositionEquiv k).symm_apply_apply (Sum.inl i)

theorem pairPositionEquiv_symm_one (k : ℕ) (i : Fin (k+2)) :
    (pairPositionEquiv k).symm (alternatingIndex i 1) = Sum.inr i :=
  (pairPositionEquiv k).symm_apply_apply (Sum.inr i)

def pairSequenceEquiv (k : ℕ) (V : Type*) :
    (Fin (k+2) → V × V) ≃ (Fin ((k+2)*2) → V) where
  toFun t j := pairTupleLabels t ((pairPositionEquiv k).symm j)
  invFun f i := (f (alternatingIndex i 0),f (alternatingIndex i 1))
  left_inv t := by
    funext i
    simp only [pairPositionEquiv_symm_zero,pairPositionEquiv_symm_one,pairTupleLabels,Prod.mk.eta]
  right_inv f := by
    funext j
    obtain ⟨s,rfl⟩ := (pairPositionEquiv k).surjective j
    cases s with
    | inl i =>
      change pairTupleLabels (fun a => (f (alternatingIndex a 0),f (alternatingIndex a 1)))
        ((pairPositionEquiv k).symm ((pairPositionEquiv k) (Sum.inl i))) = f ((pairPositionEquiv k) (Sum.inl i))
      rw [Equiv.symm_apply_apply]
      rfl
    | inr i =>
      change pairTupleLabels (fun a => (f (alternatingIndex a 0),f (alternatingIndex a 1)))
        ((pairPositionEquiv k).symm ((pairPositionEquiv k) (Sum.inr i))) = f ((pairPositionEquiv k) (Sum.inr i))
      rw [Equiv.symm_apply_apply]
      rfl

theorem pairSequenceEquiv_zero {V : Type*} {k : ℕ} (t : Fin (k+2) → V × V) (i : Fin (k+2)) :
    pairSequenceEquiv k V t (alternatingIndex i 0) = (t i).1 := by
  change pairTupleLabels t ((pairPositionEquiv k).symm (alternatingIndex i _)) = _
  simp only [pairPositionEquiv_symm_zero,pairPositionEquiv_symm_one,pairTupleLabels]

theorem pairSequenceEquiv_one {V : Type*} {k : ℕ} (t : Fin (k+2) → V × V) (i : Fin (k+2)) :
    pairSequenceEquiv k V t (alternatingIndex i 1) = (t i).2 := by
  change pairTupleLabels t ((pairPositionEquiv k).symm (alternatingIndex i _)) = _
  simp only [pairPositionEquiv_symm_zero,pairPositionEquiv_symm_one,pairTupleLabels]

def closingInterface (k : ℕ) (i : Fin (k+2)) : Bool := decide (i.val+1=k+2)

def SuccessorSequenceValid {V : Type*} {c : ℕ} (G : SimpleGraph V) (π : Equiv.Perm V)
    (f : Fin c → V) : Prop :=
  ∀ j, G.Adj (f j) (if j.val+1=c then π (f (cycleNext j)) else f (cycleNext j))

theorem successor_pair_sequence_valid {V : Type*} {k : ℕ}
    (G : SimpleGraph V) (π : Equiv.Perm V) (t : Fin (k+2) → V × V) :
    TwistedCyclicTupleValid G (fun i => choosePermutation π (closingInterface k i)) t ↔
      SuccessorSequenceValid G π (pairSequenceEquiv k V t) := by
  have hzero (i : Fin (k+2)) : (alternatingIndex i 0).val+1 ≠ (k+2)*2 := by
    change 0+2*i.val+1 ≠ (k+2)*2
    have hi := i.isLt
    omega
  have hone (i : Fin (k+2)) : (alternatingIndex i 1).val+1 = (k+2)*2 ↔ i.val+1=k+2 := by
    change 1+2*i.val+1 = (k+2)*2 ↔ i.val+1=k+2
    omega
  have hz (i : Fin (k+2)) :
      G.Adj (pairSequenceEquiv k V t (alternatingIndex i 0))
        (if (alternatingIndex i 0).val+1=(k+2)*2 then
          π (pairSequenceEquiv k V t (cycleNext (alternatingIndex i 0)))
        else pairSequenceEquiv k V t (cycleNext (alternatingIndex i 0))) ↔ G.Adj (t i).1 (t i).2 := by
    simp only [hzero,ite_false,alternatingIndex_next_zero,pairSequenceEquiv_zero,pairSequenceEquiv_one]
  have ho (i : Fin (k+2)) :
      G.Adj (pairSequenceEquiv k V t (alternatingIndex i 1))
        (if (alternatingIndex i 1).val+1=(k+2)*2 then
          π (pairSequenceEquiv k V t (cycleNext (alternatingIndex i 1)))
        else pairSequenceEquiv k V t (cycleNext (alternatingIndex i 1))) ↔
      G.Adj (t i).2 (choosePermutation π (closingInterface k i) (t (finRotate (k+2) i)).1) := by
    simp only [hone,alternatingIndex_next_one,pairSequenceEquiv_zero,pairSequenceEquiv_one]
    by_cases hh : i.val=k+1 <;> simp [choosePermutation,closingInterface,hh]
  constructor
  · intro ht j
    obtain ⟨⟨i,b⟩,rfl⟩ := finProdFinEquiv.surjective j
    fin_cases b
    · exact (hz i).mpr (ht i).1
    · exact (ho i).mpr (ht i).2
  · intro ht i
    exact ⟨(hz i).mp (ht _),(ho i).mp (ht _)⟩

theorem successor_sequence_closing_endpoint {V : Type*} {c : ℕ} (hc : 0 < c)
    (f : Fin c → V) (j : Fin c) (hj : j.val+1=c) :
    f (cycleNext j) = f ⟨0,hc⟩ := by
  congr 1
  apply Fin.ext
  simp only [cycleNext,hj,Nat.mod_self]

end Oberwolfach

namespace Oberwolfach

theorem permutationSeparated_comp_equiv {I J V : Type*} (π : Equiv.Perm V) (b : ℕ)
    (e : I ≃ J) (f : J → V) :
    PermutationSeparated π b (fun i => f (e i)) ↔ PermutationSeparated π b f := by
  constructor
  · intro h i j hij
    have hne : e.symm i ≠ e.symm j := fun he => hij (e.symm.injective he)
    simpa only [e.apply_symm_apply] using h (e.symm i) (e.symm j) hne
  · intro h i j hij
    exact h (e i) (e j) (fun he => hij (e.injective he))

theorem pairSequence_separated {V : Type*} {k : ℕ} (π : Equiv.Perm V) (b : ℕ)
    (t : Fin (k+2) → V × V) :
    PermutationSeparated π b (pairSequenceEquiv k V t) ↔
      PermutationSeparated π b (pairTupleLabels t) :=
  permutationSeparated_comp_equiv π b (pairPositionEquiv k).symm (pairTupleLabels t)

theorem pairSequence_weight_incidence {V : Type*} [Fintype V] {k : ℕ}
    (w : (Fin (k+2) → V × V) → ℝ) (E : (Fin ((k+2)*2) → V) → Prop) [DecidablePred E] :
    (∑ f, if E f then w ((pairSequenceEquiv k V).symm f) else 0) =
      ∑ t, if E (pairSequenceEquiv k V t) then w t else 0 := by
  have h := Fintype.sum_equiv (pairSequenceEquiv k V)
    (fun t => if E (pairSequenceEquiv k V t) then w t else 0)
    (fun f => if E f then w ((pairSequenceEquiv k V).symm f) else 0)
    (fun t => by rw [Equiv.symm_apply_apply])
  exact h.symm

end Oberwolfach
