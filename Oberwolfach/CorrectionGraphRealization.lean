module

public import Oberwolfach.GraphDeletion
public import Oberwolfach.BipartiteEdgeColouring

@[expose] public section

/-! Realizing integer deletion matrices as physical simple subgraphs.
Opposite orientations cannot select the same edge twice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem graph_of_suborientation {V : Type*} [Fintype V]
    (Q : SimpleGraph V) (A J : V → V → ℕ)
    (hA : ∀ x y,A x y+A y x=if Q.Adj x y then 1 else 0)
    (hJ : ∀ x y,J x y≤A x y) :
    ∃ P : SimpleGraph V,P≤Q ∧ ∀ v,P.degree v=(∑ w,J v w)+(∑ w,J w v) := by
  classical
  have hbound (x y : V) : J x y+J y x≤ if Q.Adj x y then 1 else 0 := by
    rw [← hA]
    exact Nat.add_le_add (hJ x y) (hJ y x)
  let P : SimpleGraph V := {
    Adj := fun x y=>0<J x y+J y x
    symm := ⟨by intro x y hx;simpa only [Nat.add_comm] using hx⟩
    loopless := ⟨by intro x hx;have hh:=hbound x x;simp only [SimpleGraph.irrefl,ite_false] at hh;omega⟩ }
  refine ⟨P,?_,?_⟩
  · intro x y hxy
    have hh := hbound x y
    change 0<J x y+J y x at hxy
    by_contra h
    simp only [h,ite_false] at hh
    omega
  · intro v
    rw [SimpleGraph.degree,SimpleGraph.neighborFinset_eq_filter,Finset.card_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    have hh : J v w+J w v≤1 := (hbound v w).trans (by split_ifs <;> omega)
    split_ifs with hp
    · change 0<J v w+J w v at hp
      omega
    · change ¬0<J v w+J w v at hp
      omega

theorem relation_from_submatrix {V U : Type*} [Fintype V] [Fintype U]
    (H : V → U → Prop) (K : V → U → ℕ)
    (hK : ∀ v u,K v u≤ if H v u then 1 else 0) :
    ∃ J : V → U → Prop,(∀ v u,J v u → H v u) ∧
      (∀ v,(Finset.univ.filter (J v)).card=∑ u,K v u) ∧
      (∀ u,(Finset.univ.filter (fun v=>J v u)).card=∑ v,K v u) := by
  classical
  let J (v : V) (u : U) := 0<K v u
  have hind (v : V) (u : U) : (if J v u then 1 else 0 : ℕ)=K v u := by
    have hh : K v u≤1 := (hK v u).trans (by split_ifs <;> omega)
    dsimp [J]
    split_ifs <;> omega
  refine ⟨J,?_,?_,?_⟩
  · intro v u hvu
    have hh := hK v u
    change 0<K v u at hvu
    by_contra h
    simp only [h,ite_false] at hh
    omega
  · intro v
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro u _
    split_ifs with hp
    · have hh := hind v u
      rw [if_pos hp] at hh
      exact hh
    · have hh := hind v u
      rw [if_neg hp] at hh
      exact hh
  · intro u
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs with hp
    · have hh := hind v u
      rw [if_pos hp] at hh
      exact hh
    · have hh := hind v u
      rw [if_neg hp] at hh
      exact hh

theorem relation_deleted_row_degree {V U : Type*} [Fintype V] [Fintype U]
    (H J : V → U → Prop) (hJ : ∀ v u,J v u → H v u) (v : V) :
    (Finset.univ.filter (fun u=>H v u ∧ ¬J v u)).card=
      (Finset.univ.filter (H v)).card-(Finset.univ.filter (J v)).card := by
  classical
  have hs : Finset.univ.filter (J v)⊆Finset.univ.filter (H v) := by
    intro u hu
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hJ v u (by simpa using hu)
  have heq : Finset.univ.filter (fun u=>H v u ∧ ¬J v u)=
      Finset.univ.filter (H v) \ Finset.univ.filter (J v) := by ext u;simp
  rw [heq,Finset.card_sdiff_of_subset hs]

theorem relation_deleted_column_degree {V U : Type*} [Fintype V] [Fintype U]
    (H J : V → U → Prop) (hJ : ∀ v u,J v u → H v u) (u : U) :
    (Finset.univ.filter (fun v=>H v u ∧ ¬J v u)).card=
      (Finset.univ.filter (fun v=>H v u)).card-(Finset.univ.filter (fun v=>J v u)).card :=
  relation_deleted_row_degree (fun u v=>H v u) (fun u v=>J v u) (fun u v=>hJ v u) u

theorem ordinary_degree_imbalance_even {V U : Type*} [Fintype V] [Fintype U]
    (Q : SimpleGraph V) (H : V → U → Prop) :
    Even (∑ v,((Q.degree v : ℤ)-2*(Finset.univ.filter (H v)).card)) := by
  classical
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  have hq : Even (∑ v,(Q.degree v : ℤ)) := by
    have hh : (∑ v,(Q.degree v : ℤ))=2*Q.edgeFinset.card := by
      exact_mod_cast Q.sum_degrees_eq_twice_card_edges
    rw [hh]
    exact even_two_mul _
  exact hq.sub (even_two_mul _)

end Oberwolfach
