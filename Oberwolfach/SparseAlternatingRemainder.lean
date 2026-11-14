module

public import Oberwolfach.SparseFirstCornerError
public import Oberwolfach.SparseNegativeCornerErrors

@[expose] public section

/-! The error after separating the identity and opposite-corner parts. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def sparseRemainderMap (H : A → B → Prop) (q : B → ℝ) :
    (A×B → ℝ) →ₗ[ℝ] (A×B → ℝ) := sparseAlternatingMap H q-LinearMap.id-sparseOppositeMap H q

theorem sparseRemainderMap_norm (H : A → B → Prop) (p q : B → ℝ)
    (L δ D : ℝ) (h : SparseIntersectionData H p q L δ D)
    (ha : 0<Fintype.card A) (hb : 0<Fintype.card B)
    (z : A×B → ℝ) (hz : z∈zeroMarginalSpace H) :
    ‖sparseRemainderMap H q z‖≤8*L^3*(δ+D/(Fintype.card A:ℝ)+1/(Fintype.card B:ℝ))*‖z‖ := by
  let a : ℝ := Fintype.card A
  let b : ℝ := Fintype.card B
  have ha' : 0<a := Nat.cast_pos.mpr ha
  have hb' : 0<b := Nat.cast_pos.mpr hb
  have hL := h.L_nonneg
  have hδ := h.delta_nonneg
  have hD := h.D_nonneg
  apply (pi_norm_le_iff_of_nonneg (show 0≤8*L^3*(δ+D/a+1/b)*‖z‖ by positivity)).mpr
  intro e
  rcases e with ⟨x,u⟩
  change |sparseAlternatingMap H q z (x,u)-z (x,u)-sparseOppositeMap H q z (x,u)|≤_
  by_cases hxu : H x u
  · let c₁ := q u/(a*b)*(∑ y,bipAdj H y u*bipWeightedCodegree H q x y)
    let c₂ := q u/(a*b)*(∑ y,z (y,u)*bipWeightedCodegree H q x y)
    let c₄ := (q u)^2/(a*b)*(∑ v,z (x,v)*q v*bipPairIntersection H v u)
    have h1 : |(c₁-1)*z (x,u)|≤L*(2*δ+(L^2+1)*(D/a))*‖z‖ := by
      rw [abs_mul]
      have hbz : |z (x,u)|≤‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z (x,u)
      exact mul_le_mul (sparse_first_corner_error H p q L δ D h ha hb x u) hbz
        (abs_nonneg _) (by positivity)
    have h2 : |c₂|≤L*(δ+(L^2+1)*(D/a))*‖z‖ :=
      sparse_second_corner_error H p q L δ D h ha hb z hz.2.2 x u
    have h4 : |c₄|≤L^3*(δ+2/b)*‖z‖ :=
      sparse_fourth_corner_error H p q L δ D h ha hb z hz.2.1 x u
    have he : sparseAlternatingMap H q z (x,u)-z (x,u)-sparseOppositeMap H q z (x,u)=
        (c₁-1)*z (x,u)-c₂-c₄ := by
      rw [sparseAlternatingMap_entry H q z hz.1 x u hxu]
      dsimp only [c₁,c₂,c₄]
      ring
    rw [he]
    calc
      _ ≤ |(c₁-1)*z (x,u)-c₂|+|c₄| := by
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le ((c₁-1)*z (x,u)-c₂) 0 c₄
      _ ≤ (|(c₁-1)*z (x,u)|+|c₂|)+|c₄| := by
        gcongr
        simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le ((c₁-1)*z (x,u)) 0 c₂
      _ ≤ (L*(2*δ+(L^2+1)*(D/a))+L*(δ+(L^2+1)*(D/a))+L^3*(δ+2/b))*‖z‖ := by
        nlinarith [h1,h2,h4]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simpa only [mul_div,mul_one] using sparse_first_error_scalar L δ (D/a) (1/b)
          h.one_le_L hδ (by positivity) (by positivity)
  · have hT := (sparseAlternatingMap_zero_marginals H q z).1 x u hxu
    have hK : sparseOppositeMap H q z (x,u)=0 := by
      change bipAdj H x u*(q u)^2/(a*b)*_=0
      simp only [bipAdj,hxu,ite_false,zero_mul,zero_div]
    rw [hT,hz.1 x u hxu,hK,sub_self,sub_zero,abs_zero]
    positivity

end Oberwolfach
