module

public import Oberwolfach.OrdinaryExactDecomposition
public import Oberwolfach.GraphDeletion

@[expose] public section

/-! Exact row balance and hub divisibility after removing a contained
ordinary wheel decomposition. The result uses degree subtraction on the
actual rim graph and exact subtraction of the actual spoke set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem spoke_row_sdiff_card (H K : V→U→Prop) (hKH : ∀ v u,K v u→H v u) (v : V) :
    (Finset.univ.filter (fun u=>H v u ∧ ¬K v u)).card=
      (Finset.univ.filter (H v)).card-(Finset.univ.filter (K v)).card := by
  have he : Finset.univ.filter (fun u=>H v u ∧ ¬K v u)=
      Finset.univ.filter (H v)\Finset.univ.filter (K v) := by ext u;simp
  rw [he,Finset.card_sdiff_of_subset]
  intro u hu
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
  exact hKH v u hu

theorem spoke_col_sdiff_card (H K : V→U→Prop) (hKH : ∀ v u,K v u→H v u) (u : U) :
    (Finset.univ.filter (fun v=>H v u ∧ ¬K v u)).card=
      (Finset.univ.filter (fun v=>H v u)).card-(Finset.univ.filter (fun v=>K v u)).card :=
  spoke_row_sdiff_card (fun u v=>H v u) (fun u v=>K v u) (fun u v=>hKH v u) u

theorem ordinary_decomposition_remainder_balance (Q R : SimpleGraph V) (H K : V→U→Prop)
    (r : ℕ) (hRQ : R≤Q) (hKH : ∀ v u,K v u→H v u)
    (hQ : ∀ v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hU : ∀ u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hdec : HasOrdinaryWheelDecomposition R K r) :
    (∀ v,(Q\R).degree v=2*(Finset.univ.filter (fun u=>H v u ∧ ¬K v u)).card) ∧
    (∀ u,r∣(Finset.univ.filter (fun v=>H v u ∧ ¬K v u)).card) := by
  obtain ⟨hR,hK⟩:=ordinary_wheel_decomposition_balance R K r hdec
  constructor
  · intro v
    rw [graph_degree_sdiff Q R hRQ,hQ v,hR v,spoke_row_sdiff_card H K hKH v,Nat.mul_sub_left_distrib]
  · intro u
    rw [spoke_col_sdiff_card H K hKH u]
    exact Nat.dvd_sub (hU u) (hK u)

end Oberwolfach
