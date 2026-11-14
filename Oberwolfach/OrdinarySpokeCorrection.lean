module

public import Oberwolfach.OrdinarySpokeCorrectionBounds
public import Oberwolfach.OrdinarySpokeResidual
public import Oberwolfach.OrdinaryCycleWeightRestriction

@[expose] public section

/-! The complete spoke correction, using the actual averaged wheel transfers.
Exact rim loads and degree balance supply its row-sum condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_spoke_correction {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] {r : ℕ} (hr : 3≤r)
    (Q F : SimpleGraph V) (H : V → U → Prop)
    (γ η : ℝ) (hγ : 0<γ) (hη : 0≤η) (hn : 0<Fintype.card V)
    (ψ : OrdinaryWheel Q F H r → ℝ)
    (hdeg : ∀ v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hR : ∀ x y,Q.Adj x y → ordinaryRimLoad ψ x y=1)
    (herr : ∀ v u,|ordinarySpokeResidual ψ v u|≤η)
    (hT : ∀ v (i j : {u // H v u}),i.val≠j.val →
      γ*(Fintype.card V:ℝ)^(r^2)≤
        (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ)) :
    ∃ Φ : OrdinaryWheel Q F H r → ℝ,
      (∀ x y,ordinaryRimLoad Φ x y=0) ∧
      (∀ v u,ordinarySpokeLoad Φ v u=ordinarySpokeResidual ψ v u) ∧
      (∀ D,|Φ D|≤(2*η*(6*((r:ℝ)^2)^r/γ)*(r+1))/(Fintype.card V:ℝ)^(r-1)) := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  let T (v : V) := ordinaryNeighbourTransfer hr Q F H v
  let R (v : V) := ordinaryRowCorrection v (ordinarySpokeResidual ψ v) (T v)
  have hpos (v : V) (i j : {u // H v u}) (hij : i.val≠j.val) :
      0<Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val) := by
    have hp : (0:ℝ)<γ*(Fintype.card V:ℝ)^(r^2) := by positivity
    exact_mod_cast hp.trans_le (hT v i j hij)
  have hrows (v : V) :
      (∀ x y,ordinaryRimLoad (R v) x y=0) ∧
      (∀ x u,ordinarySpokeLoad (R v) x u=
        (if x=v then (1:ℝ) else 0)*ordinarySpokeResidual ψ v u) := by
    have hz : (∑ u : {u // H v u},ordinarySpokeResidual ψ v u)=0 := by
      rw [← finite_sum_restrict_of_zero (H v) (ordinarySpokeResidual ψ v)
        (fun u hu => ordinarySpokeResidual_outside ψ v u hu)]
      exact ordinarySpokeResidual_balanced ψ hdeg hR v
    exact ordinaryRowCorrection_loads v (ordinarySpokeResidual ψ v) hz
      (fun u hu => ordinarySpokeResidual_outside ψ v u hu) (T v)
      (fun i j => (ordinaryNeighbourTransfer_loads hr Q F H v i j (hpos v)).1)
      (fun i j => (ordinaryNeighbourTransfer_loads hr Q F H v i j (hpos v)).2)
  let Φ (D : OrdinaryWheel Q F H r) : ℝ := ∑ v, (1:ℝ)*R v D
  refine ⟨Φ,?_,?_,?_⟩
  · intro x y
    change ordinaryRimLoad (fun D => ∑ v,(1:ℝ)*R v D) x y=0
    rw [ordinaryRimLoad_combination]
    simp only [fun v => (hrows v).1 x y,mul_zero,Finset.sum_const_zero]
  · intro x u
    change ordinarySpokeLoad (fun D => ∑ v,(1:ℝ)*R v D) x u=ordinarySpokeResidual ψ x u
    rw [ordinarySpokeLoad_combination]
    simp only [fun v => (hrows v).2 x u,one_mul]
    simp [eq_comm]
  · intro D
    let K : ℝ := 6*((r:ℝ)^2)^r/γ
    let B (v : V) : ℝ := if v∈(ordinaryWheelRim D).support then
      K/(Fintype.card V:ℝ)^(r-1) else K/(Fintype.card V:ℝ)^r
    have hK : 0≤K := by dsimp [K];positivity
    have hB (v : V) : 0≤B v := by dsimp [B];split_ifs <;> positivity
    have hb (v : V) : |R v D|≤2*η*B v := by
      exact ordinaryRowCorrection_bound v (ordinarySpokeResidual ψ v) (T v) D η (B v)
        hη (hB v) (herr v)
        (fun i j => ordinaryNeighbourTransfer_bound hr Q F H v i j γ hγ hn (hT v) D)
        (fun i j hi hj => ordinaryNeighbourTransfer_zero_other_hubs hr Q F H v i j D hi hj)
    have hsum : (∑ v,B v)≤K*(r+1)/(Fintype.card V:ℝ)^(r-1) := by
      have hh := finite_vertex_coefficient_sum (ordinaryWheelRim D).support.toFinset
        (show 1≤r by omega) D.val.1.val.property.support_card K hK hn
      simpa only [B,Set.mem_toFinset] using hh
    calc
      |Φ D| = |∑ v,R v D| := by simp only [Φ,one_mul]
      _ ≤ ∑ v,|R v D| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v,2*η*B v := Finset.sum_le_sum (fun v _ => hb v)
      _ = 2*η*∑ v,B v := by rw [Finset.mul_sum]
      _ ≤ 2*η*(K*(r+1)/(Fintype.card V:ℝ)^(r-1)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by dsimp [K];ring

end Oberwolfach
