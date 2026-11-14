module

public import Oberwolfach.FiniteCoordinateEvents
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

/-! Counting tuples with a conflict in two distinct coordinates. The
coordinate types can have different sizes and can be empty. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_tuple_pair_count
    {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀ j,Fintype (X j)]
    (i j : J) (hij : i≠j) (P : X i → X j → Prop) {A s : ℕ}
    (hP : ∀ a,(Finset.univ.filter (fun b=>P a b)).card≤A)
    (hsize : ∀ j,Fintype.card (X j)≤s) :
    (Finset.univ.filter (fun f : ∀ j,X j=>P (f i) (f j))).card≤
      A*s^(Fintype.card J-1) := by
  classical
  let e := Equiv.piSplitAt j X
  have hsum : (Finset.univ.filter (fun f : ∀ j,X j=>P (f i) (f j))).card=
      ∑ g : (u : {u // u≠j}) → X u.val,
        (Finset.univ.filter (fun b : X j=>P (g ⟨i,hij⟩) b)).card := by
    have hb : (Finset.univ.filter (fun f : ∀ j,X j=>P (f i) (f j))).card=
        ∑ f : ∀ j,X j,if P (f i) (f j) then (1 : ℕ) else 0 := by
      simpa only [Nat.cast_id] using
        (Finset.sum_boole (R:=ℕ) (fun f : ∀ j,X j=>P (f i) (f j)) Finset.univ).symm
    rw [hb]
    rw [← e.symm.sum_comp (fun f : ∀ j,X j=>if P (f i) (f j) then (1 : ℕ) else 0)]
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g _
    have hterm (b : X j) :
        (if P ((e.symm (b,g)) i) ((e.symm (b,g)) j) then (1 : ℕ) else 0)=
          if P (g ⟨i,hij⟩) b then 1 else 0 := by
      simp [e,Equiv.piSplitAt,hij]
    simp_rw [hterm]
    exact Finset.sum_boole _ _
  have hcard : Fintype.card ((u : {u // u≠j}) → X u.val)≤s^(Fintype.card J-1) := by
    rw [Fintype.card_pi]
    calc
      _ ≤ ∏ _u : {u // u≠j},s := Finset.prod_le_prod' (fun u _=>hsize u.val)
      _ = _ := by simp [Fintype.card_subtype_compl]
  rw [hsum]
  calc
    _ ≤ ∑ _g : (u : {u // u≠j}) → X u.val,A := Finset.sum_le_sum (fun g _=>hP (g ⟨i,hij⟩))
    _ = Fintype.card ((u : {u // u≠j}) → X u.val)*A := by simp
    _ ≤ s^(Fintype.card J-1)*A := Nat.mul_le_mul_right _ hcard
    _ = _ := Nat.mul_comm _ _

theorem finite_tuple_conflict_count
    {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type*} [∀ j,Fintype (X j)]
    (P : ∀ i j,X i → X j → Prop) {A s : ℕ}
    (hP : ∀ i j,i≠j → ∀ a,(Finset.univ.filter (fun b=>P i j a b)).card≤A)
    (hsize : ∀ j,Fintype.card (X j)≤s) :
    (Finset.univ.filter (fun f : ∀ j,X j=>∃ i j,i≠j ∧ P i j (f i) (f j))).card≤
      (Fintype.card J)^2*A*s^(Fintype.card J-1) := by
  classical
  let pairs : Finset (J×J) := Finset.univ.filter (fun p=>p.1≠p.2)
  let B := fun p : J×J=>Finset.univ.filter (fun f : ∀ j,X j=>P p.1 p.2 (f p.1) (f p.2))
  have hsub : Finset.univ.filter (fun f : ∀ j,X j=>∃ i j,i≠j ∧ P i j (f i) (f j))⊆
      pairs.biUnion B := by
    intro f hf
    obtain ⟨i,j,hij,hP⟩ := (Finset.mem_filter.mp hf).2
    exact Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP⟩⟩
  have hpairs : pairs.card≤(Fintype.card J)^2 := by
    have hh := Finset.card_le_card (show pairs⊆Finset.univ from Finset.filter_subset _ _)
    simpa only [Finset.card_univ,Fintype.card_prod,pow_two] using hh
  calc
    _ ≤ (pairs.biUnion B).card := Finset.card_le_card hsub
    _ ≤ pairs.card*(A*s^(Fintype.card J-1)) := Finset.card_biUnion_le_card_mul _ _ _
      (fun p hp=>finite_tuple_pair_count p.1 p.2 (Finset.mem_filter.mp hp).2
        (P p.1 p.2) (hP p.1 p.2 (Finset.mem_filter.mp hp).2) hsize)
    _ ≤ (Fintype.card J)^2*(A*s^(Fintype.card J-1)) := Nat.mul_le_mul_right _ hpairs
    _ = _ := by ring

end Oberwolfach
