module

public import Oberwolfach.MixedGreedySequences
public import Oberwolfach.SuccessorTupleRepresentation
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-! The endpoint-first order used to count the two kinds of common marked
paths. Both roots are excluded at every free choice, but are not required
to be separated from one another. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def pathChoiceOrder (r : ℕ) : Equiv.Perm (Fin (r+2)) :=
  (finSuccEquiv (r+1)).trans ((Equiv.optionCongr (finRotate (r+1))).trans (finSuccEquiv (r+1)).symm)

theorem pathChoiceOrder_zero (r : ℕ) : pathChoiceOrder r 0=0 := by simp [pathChoiceOrder]

theorem pathChoiceOrder_succ (r : ℕ) (i : Fin (r+1)) :
    pathChoiceOrder r i.succ=(finRotate (r+1) i).succ := by simp [pathChoiceOrder]

theorem pathChoiceOrder_last (r : ℕ) : pathChoiceOrder r (Fin.last (r+1))=1 := by
  change pathChoiceOrder r (Fin.last r).succ=1
  rw [pathChoiceOrder_succ,finRotate_last]
  rfl

theorem pathChoiceOrder_middle (r : ℕ) (i : Fin r) :
    pathChoiceOrder r i.castSucc.succ=i.succ.succ := by
  rw [pathChoiceOrder_succ]
  exact congrArg Fin.succ (finRotate_of_lt i.isLt)

def markedPathChoiceClass {V : Type*} (j : Bool) (T₀ TK : Finset V) (n : ℕ) : Finset V :=
  if j=false ∧ n=3 then TK else T₀

def markedPathChoiceHead {V : Type*} (π : Equiv.Perm V) (j : Bool) (n : ℕ) : Equiv.Perm V :=
  if j=false ∧ n=3 then π else Equiv.refl V

def markedPathChoiceRequests {V : Type*} [DecidableEq V] (π : Equiv.Perm V) (j : Bool)
    (m : ℕ) (v v' : V) (n : ℕ) (f : Fin n→V) : Finset V :=
  if n=0 then {v,v'} else
  if n=1 then {if j then π v else v,if j then π v' else v'} else
  if h : n=2 then {f ⟨0,by omega⟩} else
  if h : 2<n then {f ⟨n-1,by omega⟩} ∪ (if n+1=m then {f ⟨1,by omega⟩} else ∅) else ∅

theorem markedPathChoiceRequests_card {V : Type*} [DecidableEq V]
    (π : Equiv.Perm V) (j : Bool) (m : ℕ) (v v' : V) (n : ℕ) (f : Fin n→V) :
    (markedPathChoiceRequests π j m v v' n f).card≤2 := by
  have hp (x y : V) : ({x,y}:Finset V).card≤2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  unfold markedPathChoiceRequests
  split_ifs <;> first | exact hp _ _ | simp | exact (Finset.card_union_le _ _).trans (by simp)

theorem marked_path_choice_count {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b m : ℕ) (j : Bool)
    (T₀ TK : Finset V) (v v' : V) (α a : ℝ) (hα : 0≤α) (hα1 : α≤1) (ha : 0≤a)
    (hbudget : a≤α*min (T₀.card:ℝ) TK.card-((m:ℝ)+2)*(2*(b:ℝ)+1))
    (hdeg₀ : ∀ x : V,(1/2+α/2)*T₀.card≤((P.neighborFinset x∩T₀).card:ℝ))
    (hdegK : ∀ x : V,(1/2+α/2)*TK.card≤((P.neighborFinset x∩TK.image π).card:ℝ)) :
    a^m≤(Fintype.card {f : Fin m→V //
      MixedGreedyGood P π b (markedPathChoiceClass j T₀ TK) (markedPathChoiceHead π j)
        (markedPathChoiceRequests π j m v v') {v,v'} f}:ℝ) := by
  apply mixed_greedy_sequence_count P π b (markedPathChoiceClass j T₀ TK) (markedPathChoiceHead π j)
    (markedPathChoiceRequests π j m v v') {v,v'} m α a hα1 ha
  · intro n _
    have hmin : min (T₀.card:ℝ) TK.card≤(markedPathChoiceClass j T₀ TK n).card := by
      unfold markedPathChoiceClass;split_ifs
      · exact min_le_right _ _
      · exact min_le_left _ _
    have hcard : (({v,v'}:Finset V).card:ℝ)≤2 := by
      have hh : ({v,v'}:Finset V).card≤2 := (Finset.card_insert_le _ _).trans (by simp)
      exact_mod_cast hh
    have hmul := mul_le_mul_of_nonneg_left hmin hα
    have hdel := mul_le_mul_of_nonneg_right hcard (show 0≤2*(b:ℝ)+1 by positivity)
    nlinarith only [hbudget,hmul,hdel]
  · intro n _ x
    unfold markedPathChoiceClass markedPathChoiceHead
    split_ifs
    · exact hdegK x
    · simpa using hdeg₀ x
  · intro n _ f _;exact markedPathChoiceRequests_card π j m v v' n f

end Oberwolfach
