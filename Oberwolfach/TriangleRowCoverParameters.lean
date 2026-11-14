module

public import Oberwolfach.EndpointFactorUnderDeletion

@[expose] public section

/-! Choose the number of triangle row roots before the ambient order.
The degree-three accumulated deletion fits both fixed-domain count errors
and the fixed potential-load error. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach

theorem triangle_row_cover_parameters (ε η κ C : ℝ)
    (hε:0<ε) (hη:0<η) (hκ:0<κ) (hC:0<C) :
    ∃ θ:ℝ,0<θ ∧ ∀ a b n:ℝ,0<a → κ*a≤b → 0≤n → n≤θ*a →
      4*(3*n)/a+3*(3*n)/b≤ε/2 ∧ 5*C*(3*n)/a≤η/2 := by
  let D:ℝ:=12+9/κ
  have hD:0<D:=by dsimp [D];positivity
  let θ:=min (ε/(2*D)) (η/(30*C))
  have hθ:0<θ:=lt_min (by positivity) (by positivity)
  refine ⟨θ,hθ,?_⟩
  intro a b n ha hba hn hnθ
  have hb:0<b:=(mul_pos hκ ha).trans_le hba
  have hratio:n/a≤θ:=(div_le_iff₀ ha).mpr hnθ
  have hnb:n/b≤(n/a)/κ:=by
    rw [div_div]
    apply div_le_div_of_nonneg_left hn (mul_pos ha hκ)
    simpa only [mul_comm] using hba
  constructor
  · have h₁:D*(n/a)≤D*θ:=mul_le_mul_of_nonneg_left hratio hD.le
    have h₂:D*θ≤ε/2:=by
      have hh:=mul_le_mul_of_nonneg_left (min_le_left (ε/(2*D)) (η/(30*C))) hD.le
      have he:D*(ε/(2*D))=ε/2:=by field_simp <;> ring
      simpa only [θ,he] using hh
    calc
      _ = 12*(n/a)+9*(n/b):=by ring
      _ ≤ 12*(n/a)+9*((n/a)/κ):=add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hnb (by norm_num : (0:ℝ)≤9))
      _ = D*(n/a):=by dsimp [D];ring
      _ ≤ ε/2:=h₁.trans h₂
  · have h₁:15*C*(n/a)≤15*C*θ:=mul_le_mul_of_nonneg_left hratio (by positivity)
    have h₂:15*C*θ≤η/2:=by
      have hh:=mul_le_mul_of_nonneg_left (min_le_right (ε/(2*D)) (η/(30*C))) (show 0≤15*C by positivity)
      have he:15*C*(η/(30*C))=η/2:=by field_simp <;> ring
      simpa only [θ,he] using hh
    have he:5*C*(3*n)/a=15*C*(n/a):=by ring
    rw [he]
    exact h₁.trans h₂

end Oberwolfach
