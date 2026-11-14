module

public import Oberwolfach.OrdinaryNeighbourTransfer
public import Oberwolfach.PairTransferCoefficientBound

@[expose] public section

/-! The coefficient cost of row corrections and their sum over rim vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinaryRowCorrection_bound {V U : Type*} [Fintype U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ} (v : V)
    (z : U → ℝ) (T : {u // H v u} → {u // H v u} → OrdinaryWheel Q F H r → ℝ)
    (D : OrdinaryWheel Q F H r) (η B : ℝ) (hη : 0≤η) (hB : 0≤B)
    (hz : ∀ u,|z u|≤η) (hT : ∀ i j,|T i j D|≤B)
    (hs : ∀ i j,ordinaryWheelHub D≠i.val → ordinaryWheelHub D≠j.val → T i j D=0) :
    |ordinaryRowCorrection v z T D|≤2*η*B := by
  let g : {u // H v u} ↪ U := ⟨Subtype.val,Subtype.val_injective⟩
  have hh := normalized_pair_transfer_bound g (ordinaryWheelHub D)
    (fun i => z i.val) (fun i j => T i j D) η B hη hB (fun i => hz i.val) hT hs
  convert hh using 1
  congr 1
  unfold ordinaryRowCorrection
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem finite_vertex_coefficient_sum {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) {r : ℕ} (hr : 1≤r) (hS : S.card=r)
    (K : ℝ) (hK : 0≤K) (hn : 0<Fintype.card V) :
    (∑ v : V,if v∈S then K/(Fintype.card V:ℝ)^(r-1)
      else K/(Fintype.card V:ℝ)^r)≤K*(r+1)/(Fintype.card V:ℝ)^(r-1) := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hfirst : (∑ v : V,if v∈S then K/(Fintype.card V:ℝ)^(r-1) else 0)=
      (r:ℝ)*(K/(Fintype.card V:ℝ)^(r-1)) := by
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun v => v∈S)=S := by ext;simp
    rw [hf,Finset.sum_const,hS,nsmul_eq_mul]
  have hp : (Fintype.card V:ℝ)^r=(Fintype.card V:ℝ)^(r-1)*(Fintype.card V:ℝ) := by
    rw [← pow_succ,show r-1+1=r by omega]
  calc
    _ ≤ ∑ v : V,((if v∈S then K/(Fintype.card V:ℝ)^(r-1) else 0)+
        K/(Fintype.card V:ℝ)^r) := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs
      · exact le_add_of_nonneg_right (by positivity)
      · simp only [zero_add,le_refl]
    _ = (r:ℝ)*(K/(Fintype.card V:ℝ)^(r-1))+
        (Fintype.card V:ℝ)*(K/(Fintype.card V:ℝ)^r) := by
      rw [Finset.sum_add_distrib,hfirst,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ = _ := by rw [hp];field_simp

end Oberwolfach
