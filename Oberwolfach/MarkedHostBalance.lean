module

public import Oberwolfach.MarkedWheelBalance

@[expose] public section

/-! The manuscript's three degree identities imply balance of the unit rim
vector. In particular its type ratio is derived by summing spoke degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem occurrenceSumLinear_one {V E : Type*} [Fintype E] [DecidableEq V]
    (f : E → V) (v : V) : occurrenceSumLinear f (fun _ => (1:ℝ)) v=occurrenceDegree f v := by
  unfold occurrenceSumLinear occurrenceDegree
  dsimp only [LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> rfl

theorem marked_unit_balance_of_spoke_degrees {V U E K : Type*} [Fintype V] [Fintype U]
    [Fintype E] [Fintype K] [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ)
    (H₀ Hₖ : V → U → Prop)
    (hdir : ∀ v,occurrenceDegree (Sum.elim tail ktail) v=occurrenceDegree (Sum.elim head khead) v)
    (hK : ∀ v,occurrenceDegree khead v=∑ u,if Hₖ v u then (1:ℝ) else 0)
    (hout : ∀ v,occurrenceDegree (Sum.elim tail ktail) v=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if Hₖ v u then (1:ℝ) else 0))
    (hhub : ∀ u,(∑ v,if H₀ v u then (1:ℝ) else 0)=(m:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0)) :
    (fun _ : E⊕K => (1:ℝ))∈markedBalanceSubspace tail head ktail khead m := by
  constructor
  · funext v
    rw [occurrenceSumLinear_one,occurrenceSumLinear_one]
    exact hdir v
  · have hksum : (Fintype.card K:ℝ)=∑ v,∑ u,if Hₖ v u then (1:ℝ) else 0 := by
      rw [← occurrenceDegree_total khead]
      exact Finset.sum_congr rfl (fun v _ => hK v)
    have houtsum : (Fintype.card E:ℝ)+Fintype.card K=
        (∑ v,∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ v,∑ u,if Hₖ v u then (1:ℝ) else 0) := by
      calc
        _ = (Fintype.card (E⊕K):ℝ) := by simp
        _ = ∑ v,occurrenceDegree (Sum.elim tail ktail) v := (occurrenceDegree_total _).symm
        _ = _ := by simp only [hout,Finset.sum_add_distrib]
    have hratio : (∑ v,∑ u,if H₀ v u then (1:ℝ) else 0)=
        (m:ℝ)*(∑ v,∑ u,if Hₖ v u then (1:ℝ) else 0) := by
      calc
        _ = ∑ u,∑ v,if H₀ v u then (1:ℝ) else 0 := Finset.sum_comm
        _ = ∑ u,(m:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0) := Finset.sum_congr rfl (fun u _ => hhub u)
        _ = (m:ℝ)*(∑ u,∑ v,if Hₖ v u then (1:ℝ) else 0) := by rw [Finset.mul_sum]
        _ = _ := by rw [Finset.sum_comm]
    change (∑ _e : E,(1:ℝ))=(m:ℝ)*(∑ _e : K,(1:ℝ))
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    rw [← hksum] at hratio houtsum
    rw [hratio] at houtsum
    linarith

end Oberwolfach
