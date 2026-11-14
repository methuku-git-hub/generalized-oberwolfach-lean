module

public import Oberwolfach.RootedPredecessorGraphs

@[expose] public section

/-! The explicit order for a transfer configuration: first the base cycle,
then, in each row, its two endpoints followed by the internal path vertices.
The triangle case has three earlier neighbours; all other cases have at most two. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def transferColumnOrder (r j : ℕ) : ℕ :=
  if j=1 then 0 else if j=r-1 then 1 else j

theorem transferColumnOrder_bound (r j : ℕ) (hr : 3 ≤ r) (hj : 0 < j) (hjr : j < r) :
    transferColumnOrder r j < r-1 := by
  unfold transferColumnOrder
  split_ifs  <;>  omega

theorem transferColumnOrder_injective (r j l : ℕ) (hr : 3 ≤ r)
    (hj : 0 < j) (hjr : j < r) (hl : 0 < l) (hlr : l < r)
    (he : transferColumnOrder r j=transferColumnOrder r l) : j=l := by
  unfold transferColumnOrder at he
  split_ifs at he  <;>  omega

def transferVertexPosition (r : ℕ) (i j : Fin r) : ℕ :=
  if (j:ℕ)=0 then (i:ℕ)+1 else r+1+(i:ℕ)*(r-1)+transferColumnOrder r j

theorem transferVertexPosition_bounds (r : ℕ) (hr : 3 ≤ r) (i j : Fin r) :
    0 < transferVertexPosition r i j ∧ transferVertexPosition r i j ≤ r^2 := by
  unfold transferVertexPosition
  split_ifs with hj
  · constructor
    · omega
    · have hi := i.isLt
      nlinarith
  · have hj0 : 0 < (j:ℕ) := by omega
    have hc := transferColumnOrder_bound r j hr hj0 j.isLt
    have hi := i.isLt
    have hrm : r-1+1=r := by omega
    constructor
    · omega
    · nlinarith

theorem transferVertexPosition_injective (r : ℕ) (hr : 3 ≤ r) :
    Function.Injective (fun a : Fin r×Fin r=> transferVertexPosition r a.1 a.2) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ he
  change transferVertexPosition r i j=transferVertexPosition r i' j' at he
  change (i,j)=(i',j')
  unfold transferVertexPosition at he
  by_cases hj : (j:ℕ)=0  <;>  by_cases hj' : (j':ℕ)=0
  · simp only [hj,hj',ite_true] at he
    exact Prod.ext (Fin.ext (Nat.add_right_cancel he)) (Fin.ext (hj.trans hj'.symm))
  · simp only [hj,hj',ite_true,ite_false] at he
    have hi := i.isLt
    omega
  · simp only [hj,hj',ite_true,ite_false] at he
    have hi := i'.isLt
    omega
  · simp only [hj,hj',ite_false] at he
    have hpos : 0 < (j:ℕ) := by omega
    have hpos' : 0 < (j':ℕ) := by omega
    have hc := transferColumnOrder_bound r j hr hpos j.isLt
    have hc' := transferColumnOrder_bound r j' hr hpos' j'.isLt
    have hii : (i:ℕ)=(i':ℕ) := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt|hlt
      · have hd : (i:ℕ)+1 ≤ i' := by omega
        have hm := Nat.mul_le_mul_right (r-1) hd
        nlinarith
      · have hd : (i':ℕ)+1 ≤ i := by omega
        have hm := Nat.mul_le_mul_right (r-1) hd
        nlinarith
    have hjj : (j:ℕ)=(j':ℕ) := transferColumnOrder_injective r j j' hr hpos j.isLt hpos' j'.isLt (by rw [hii] at he; omega)
    exact Prod.ext (Fin.ext hii) (Fin.ext hjj)

def transferPredecessors (r z : ℕ) : Finset ℕ :=
  if z=0 then ∅ else if z ≤ r then
    if z=1 then ∅ else if z=r then {1,z-1} else {z-1}
  else
    let j := (z-r-1)%(r-1)
    let b := (z-r-1)/(r-1)+1
    if j=0 then {0,b} else if j=1 then
      if r=3 then {0,b,z-1} else {0,b}
    else {if j=2 then z-j else z-1}∪(if j=r-2 then {z-j+1} else ∅)

theorem transferPredecessors_earlier (r : ℕ) (hr : 3 ≤ r) :
    ∀ z,∀ x∈transferPredecessors r z,x < z := by
  intro z x hx
  unfold transferPredecessors at hx
  by_cases hz : z=0
  · simp only [hz,ite_true,Finset.notMem_empty] at hx
  simp only [hz,ite_false] at hx
  by_cases hzr : z ≤ r
  · simp only [hzr,ite_true] at hx
    split_ifs at hx with hz1 hzr'
    · exact False.elim (Finset.notMem_empty x hx)
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      omega
    · simp only [Finset.mem_singleton] at hx
      omega
  · simp only [hzr,ite_false] at hx
    have hdiv := Nat.div_le_self (z-r-1) (r-1)
    have hmod := Nat.mod_lt (z-r-1) (show 0 < r-1 by omega)
    split_ifs at hx  <;>  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hx  <;>  omega

theorem transferPredecessors_card (r z : ℕ) (hr : 3 ≤ r) :
    (transferPredecessors r z).card ≤ if r=3 then 3 else 2 := by
  unfold transferPredecessors
  dsimp only
  split_ifs
  all_goals try simp only [Finset.card_empty,Finset.card_singleton,
    Finset.union_empty,Finset.singleton_union]
  all_goals first
    | omega
    | exact Finset.card_le_two
    | exact Finset.card_le_three
    | exact le_trans Finset.card_le_two (show 2≤3 by omega)

end Oberwolfach
