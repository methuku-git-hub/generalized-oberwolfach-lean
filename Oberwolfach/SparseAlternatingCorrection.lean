module

public import Oberwolfach.SparseErrorContraction
public import Oberwolfach.SecondOrderInverse
public import Oberwolfach.AlternatingCoefficientLoads

@[expose] public section

/-! The complete deterministic alternating-correction theorem with
explicit constants and actual ordered four-cycle coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def FourCycleIncident {H : A → B → Prop} (Q : BipartiteFourCycle H) (e : A×B) : Prop :=
  (e.1=Q.val.1.1 ∨ e.1=Q.val.1.2) ∧ (e.2=Q.val.2.1 ∨ e.2=Q.val.2.2)

theorem bipartiteFourCycleVector_abs {H : A → B → Prop} (Q : BipartiteFourCycle H) (e : A×B) :
    |bipartiteFourCycleVector Q e|=(if FourCycleIncident Q e then (1:ℝ) else 0) := by
  rcases Q with ⟨⟨⟨x,y⟩,⟨u,v⟩⟩,hxy,huv,hxu,hyu,hyv,hxv⟩
  rcases e with ⟨a,b⟩
  unfold bipartiteFourCycleVector alternatingRectangle FourCycleIncident
  dsimp only
  split_ifs <;> simp_all

theorem sparse_alternating_correction_inverse_profile (H : A → B → Prop) (p q : B → ℝ)
    (L δ D : ℝ) (h : SparseIntersectionData H p q L δ D)
    (ha : 0<Fintype.card A) (hb : 0<Fintype.card B)
    (hsmall : δ+D/(Fintype.card A:ℝ)+1/(Fintype.card B:ℝ)≤1/(200*L^6))
    (z : A×B → ℝ) (hz : z∈zeroMarginalSpace H) :
    ∃ t : BipartiteFourCycle H → ℝ,
      (∀ e,z e=∑ Q,t Q*bipartiteFourCycleVector Q e) ∧
      (∀ e,(∑ Q,if FourCycleIncident Q e then |t Q| else 0)≤8*L^3*(1+9*L^3)*‖z‖) := by
  let S := zeroMarginalSpace H
  let T : S →ₗ[ℝ] S :=
    { toFun := fun w=>⟨sparseAlternatingMap H q w.val,sparseAlternatingMap_zero_marginals H q w.val⟩
      map_add' := by intro w w';apply Subtype.ext;exact (sparseAlternatingMap H q).map_add w.val w'.val
      map_smul' := by intro c w;apply Subtype.ext;exact (sparseAlternatingMap H q).map_smul c w.val }
  have herror (w : S) : ‖w-T w‖≤9*L^3*‖w‖ ∧ ‖(w-T w)-T (w-T w)‖≤(1/2:ℝ)*‖w‖ :=
    sparse_error_contraction H p q L δ D h ha hb hsmall w.val w.property
  obtain ⟨w,hw,hnorm⟩ := second_order_inverse T (9*L^3) (1/2) (by norm_num)
    (fun w=>(herror w).1) (fun w=>(herror w).2) ⟨z,hz⟩
  let t (Q : BipartiteFourCycle H) := sparseRectangleCoefficient H q w.val Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2
  refine ⟨t,?_,?_⟩
  · intro e
    have he : sparseAlternatingMap H q w.val e=z e := congrFun (congrArg Subtype.val hw) e
    rw [← he]
    exact rectangleCombination_fourCycles H (sparseRectangleCoefficient H q w.val)
      (sparseRectangleCoefficient_supported H q w.val) e
  · intro e
    have hload := sparseAlternating_coefficient_load H q w.val L h.L_nonneg h.inverse_bounds ha hb e
    have he : (∑ Q,if FourCycleIncident Q e then |t Q| else 0)=
        (∑ Q,|t Q| * |bipartiteFourCycleVector Q e|) := by
      simp only [bipartiteFourCycleVector_abs,mul_ite,mul_one,mul_zero]
    rw [he]
    calc
      _ ≤ 4*L^3*‖w.val‖ := hload
      _ ≤ 4*L^3*(((1+9*L^3)/(1-(1/2:ℝ)))*‖z‖) :=
        mul_le_mul_of_nonneg_left hnorm (by have := h.L_nonneg;positivity)
      _ = _ := by ring

end Oberwolfach
