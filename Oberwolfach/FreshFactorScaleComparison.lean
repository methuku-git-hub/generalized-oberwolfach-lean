module

public import Oberwolfach.ResourceRootOmittedLoads
public import Mathlib.Tactic

@[expose] public section

/-! Scale conversion for a retained set and a subsequent alteration.
No probabilistic condition is imposed on the altered set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V C:Type*} [Fintype V] [DecidableEq V] [Fintype C]

theorem resourceRootOmittedLoad_div (R:C→Finset V) (w:C→ℝ)
    (keep:V→Prop) (v:V) (p:ℝ):
    resourceRootOmittedLoad R (fun i=>w i/p) keep v=
      resourceRootOmittedLoad R w keep v/p:=by
  unfold resourceRootOmittedLoad
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem omitted_load_rescaling_error (x y p ε η:ℝ) (hp:0<p)
    (herr:|x-p*y|≤ε*p) (hy:|1-y|≤η):|1-x/p|≤η+ε:=by
  have h₁:=abs_le.mp herr
  have h₂:=abs_le.mp hy
  have hlo:y-ε≤x/p:=(le_div_iff₀ hp).mpr (by nlinarith only [h₁.1])
  have hhi:x/p≤y+ε:=(div_le_iff₀ hp).mpr (by nlinarith only [h₁.2])
  apply abs_le.mpr
  constructor <;> linarith only [hlo,hhi,h₂.1,h₂.2]

theorem altered_profile_scale_bounds (c:ℕ) (hc:1≤c) (A Y:Finset V) (k:ℕ) (s ζ:ℝ)
    (hs:0<s) (hζ:0≤ζ) (hζ4:ζ≤1/4)
    (hA:|(A.card:ℝ)-s|≤s/4)
    (hchange:(((A\Y).card+(Y\A).card:ℕ):ℝ)≤ζ*s)
    (hY:Y.card=c*k):
    s≤2*(c:ℝ)*k ∧ (k:ℝ)≤2*s ∧ 0<(k:ℝ):=by
  have hYc:(Y.card:ℝ)=(c:ℝ)*k:=by exact_mod_cast hY
  have h₁:(A.card:ℝ)≤(Y.card:ℝ)+(A\Y).card:=by
    exact_mod_cast (show A.card≤Y.card+(A\Y).card by
      simpa only [Nat.add_comm] using Finset.card_le_card_sdiff_add_card (s:=A) (t:=Y))
  have h₂:(Y.card:ℝ)≤(A.card:ℝ)+(Y\A).card:=by
    exact_mod_cast (show Y.card≤A.card+(Y\A).card by
      simpa only [Nat.add_comm] using Finset.card_le_card_sdiff_add_card (s:=Y) (t:=A))
  have hΔA:((A\Y).card:ℝ)≤ζ*s:=by
    have ht:((A\Y).card:ℝ)≤((A\Y).card+(Y\A).card:ℕ):=by exact_mod_cast Nat.le_add_right (A\Y).card (Y\A).card
    exact ht.trans hchange
  have hΔY:((Y\A).card:ℝ)≤ζ*s:=by
    have ht:((Y\A).card:ℝ)≤((A\Y).card+(Y\A).card:ℕ):=by exact_mod_cast Nat.le_add_left (Y\A).card (A\Y).card
    exact ht.trans hchange
  have hζs:=mul_le_mul_of_nonneg_right hζ4 hs.le
  have hAs:=abs_le.mp hA
  have hcR:(1:ℝ)≤c:=by exact_mod_cast hc
  have hck:(k:ℝ)≤(c:ℝ)*k:=by nlinarith only [mul_le_mul_of_nonneg_right hcR (Nat.cast_nonneg k)]
  rw [hYc] at h₁ h₂
  have hlo:s≤2*(c:ℝ)*k:=by linarith
  have hhi:(k:ℝ)≤2*s:=by linarith
  refine ⟨hlo,hhi,?_⟩
  by_contra hn
  have hz:(k:ℝ)=0:=le_antisymm (not_lt.mp hn) (Nat.cast_nonneg k)
  rw [hz,mul_zero] at hlo
  exact (not_le.mpr hs) hlo

theorem fresh_weight_scale_bounds (d:ℕ) (c k s b B w:ℝ)
    (hc:0<c) (hk:0<k) (hs:0<s) (hb:0≤b) (hB:0≤B)
    (hsk:s≤2*c*k) (hks:k≤2*s) (hw:b/s^d≤w ∧ w≤B/s^d):
    (b/(2*c)^d)/k^d≤w ∧ w≤((2:ℝ)^d*B)/k^d:=by
  constructor
  · apply le_trans _ hw.1
    rw [div_div,←mul_pow]
    exact div_le_div_of_nonneg_left hb (pow_pos hs _) (pow_le_pow_left₀ hs.le hsk _)
  · apply hw.2.trans
    apply (div_le_div_iff₀ (pow_pos hs _) (pow_pos hk _)).mpr
    have hh:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk.le hks d) hB
    rw [mul_pow] at hh
    nlinarith only [hh]

end Oberwolfach
