module

public import Mathlib.Tactic

@[expose] public section
/-! The root-cover error can be selected after the vortex and the trace
    rate, independently of the separate bound for its physical degree. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_root_error_budget
    (ε a rate cap:ℝ) (hε:0<ε) (ha:0<a) (hrate:0<rate) (hcap:0<cap):
    ∃ξ:ℝ,0<ξ ∧ ξ≤ε/100 ∧ 80*ξ≤a^2 ∧ 10*ξ≤rate ∧ ξ≤cap ∧
      ∀(V U:Type) [Fintype V] [Fintype U] (I:Finset V),
        10*ξ*(I.card:ℝ)≤rate*Fintype.card (V⊕U) :=by
  let ξ:ℝ:=min (ε/200) (min (a^2/160) (min (rate/20) cap))
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hεξ:ξ≤ε/100:=by
    have h:=min_le_left (ε/200) (min (a^2/160) (min (rate/20) cap))
    dsimp [ξ];linarith
  have haξ:80*ξ≤a^2:=by
    have h:ξ≤a^2/160:=(min_le_right _ _).trans (min_le_left _ _)
    nlinarith [sq_nonneg a]
  have hrateξ:10*ξ≤rate:=by
    have h:ξ≤rate/20:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  have hcapξ:ξ≤cap:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ξ,hξ,hεξ,haξ,hrateξ,hcapξ,?_⟩
  intro V U _ _ I
  have hcard:(I.card:ℝ)≤Fintype.card (V⊕U):=by
    have hI:I.card≤Fintype.card V:=Finset.card_le_univ I
    have hI':(I.card:ℝ)≤Fintype.card V:=by exact_mod_cast hI
    simp only [Fintype.card_sum,Nat.cast_add]
    have hu:(0:ℝ)≤Fintype.card U:=by positivity
    linarith
  have hI0:(0:ℝ)≤I.card:=by positivity
  have hrate0:0≤rate:=hrate.le
  calc
    10*ξ*(I.card:ℝ)≤rate*(I.card:ℝ):=mul_le_mul_of_nonneg_right hrateξ hI0
    _≤rate*Fintype.card (V⊕U):=mul_le_mul_of_nonneg_left hcard hrate0
end Oberwolfach
