module

public import Oberwolfach.CommonClassBalanceBounds

@[expose] public section

/-! Actual class sizes and the marked-outgoing/ordinary-spoke gap after
physical sampling and the two later packings. Parent classes stay fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampled_class_after_change_error {A:Type} [DecidableEq A]
    (S T R:Finset A) (p e c:ℝ)
    (hT:|(T.card:ℝ)-p*S.card|≤e) (hR:((changed R T).card:ℝ)≤c):
    |(R.card:ℝ)-p*S.card|≤e+c:=by
  have hchange:|(R.card:ℝ)-T.card|≤c:=(card_difference_le_changed R T).trans hR
  calc
    _≤|(R.card:ℝ)-T.card|+|(T.card:ℝ)-p*S.card|:=abs_sub_le _ _ _
    _≤e+c:=by linarith

theorem marked_boundary_class_size_margins (a g:ℝ) (ha:0<a) (hg:0<g):
    ∃ η pmax:ℝ,0<η∧0<pmax∧pmax≤1∧∀ p:ℝ,0<p→p≤pmax→
    ∀ n:ℕ,
    (∀ {A:Type} [DecidableEq A] (S T R:Finset A),
      a*n≤(S.card:ℝ)→(S.card:ℝ)≤n→
      |(T.card:ℝ)-p*S.card|≤η*p*n→((changed R T).card:ℝ)≤(p^9+p^3)*n→
      (a/2)*p*n≤(R.card:ℝ)∧(R.card:ℝ)≤2*p*n)∧
    (∀ {A B:Type} [DecidableEq A] [DecidableEq B] (S₀ T₀ R₀:Finset A) (S₁ T₁ R₁:Finset B),
      (S₁.card:ℝ)+g*n≤S₀.card→
      |(T₀.card:ℝ)-p*S₀.card|≤η*p*n→|(T₁.card:ℝ)-p*S₁.card|≤η*p*n→
      ((changed R₀ T₀).card:ℝ)≤(p^9+p^3)*n→((changed R₁ T₁).card:ℝ)≤(p^9+p^3)*n→
      (R₁.card:ℝ)+(g/2)*p*n≤R₀.card):=by
  let η:=min (1/4) (min (a/8) (g/8))
  have hη:0<η:=lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hη1:η≤1/4:=min_le_left _ _
  have hηa:η≤a/8:=(min_le_right _ _).trans (min_le_left _ _)
  have hηg:η≤g/8:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η,min 1 (η/2),hη,lt_min (by norm_num) (by positivity),min_le_left _ _,?_⟩
  intro p hp hpp n
  have hp1:p≤1:=hpp.trans (min_le_left _ _)
  have hpη:p≤η/2:=hpp.trans (min_le_right _ _)
  have hp2:p^2≤p:=by nlinarith only [hp.le,hp1]
  have hp9:p^9≤p^3:=pow_le_pow_of_le_one hp.le hp1 (by omega)
  have hchange:(p^9+p^3)*(n:ℝ)≤η*p*n:=by
    have h9:=mul_le_mul_of_nonneg_right hp9 (Nat.cast_nonneg n: (0:ℝ)≤n)
    have h:=mul_le_mul_of_nonneg_right (hp2.trans hpη) (show 0≤p*n by positivity)
    nlinarith only [h9,h]
  have herr {A:Type} [DecidableEq A] (S T R:Finset A)
      (hT:|(T.card:ℝ)-p*S.card|≤η*p*n) (hR:((changed R T).card:ℝ)≤(p^9+p^3)*n):
      |(R.card:ℝ)-p*S.card|≤2*η*p*n:=by
    have h:=sampled_class_after_change_error S T R p (η*p*n) (η*p*n) hT (hR.trans hchange)
    linarith only [h]
  constructor
  · intro A _ S T R hS hSmax hT hR
    have hr:=abs_le.mp (herr S T R hT hR)
    have hlo:=mul_le_mul_of_nonneg_left hS hp.le
    have hhi:=mul_le_mul_of_nonneg_left hSmax hp.le
    have he1:=mul_le_mul_of_nonneg_right hη1 (show 0≤p*n by positivity)
    have hea:=mul_le_mul_of_nonneg_right hηa (show 0≤p*n by positivity)
    have hpos:0≤a*p*n:=by positivity
    have hpn:0≤p*n:=by positivity
    constructor <;> nlinarith only [hr.1,hr.2,hlo,hhi,he1,hea,hpos,hpn]
  · intro A B _ _ S₀ T₀ R₀ S₁ T₁ R₁ hgap hT₀ hT₁ hR₀ hR₁
    have h₀:=(abs_le.mp (herr S₀ T₀ R₀ hT₀ hR₀)).1
    have h₁:=(abs_le.mp (herr S₁ T₁ R₁ hT₁ hR₁)).2
    have hgap':=mul_le_mul_of_nonneg_left hgap hp.le
    have he:=mul_le_mul_of_nonneg_right hηg (show 0≤p*n by positivity)
    nlinarith only [h₀,h₁,hgap',he]
end Oberwolfach
