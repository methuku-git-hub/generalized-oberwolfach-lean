module

public import Oberwolfach.PairHubDensityBounds

@[expose] public section
/-! Density products for bounded sets of rim and hub roots. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
variable {V U Color:Type} [Fintype U] [DecidableEq V] [DecidableEq U]
theorem ordinary_root_density (h:ℕ) (p pmin smin:ℝ) (s:U→Color→ℝ) (j:Color)
    (hpmin:0<pmin) (hp:pmin≤p) (hp1:p≤1)
    (hsmin:0<smin) (hsmin1:smin≤1) (hs:∀ u,smin≤s u j):
    ∀ (S:Finset V) (J:Finset U),S.card≤h→J.card≤h→
      pmin^h*smin^h≤p^S.card*(∏ u∈J,s u j) := by
  intro S J hS hJ
  have hpmin1:pmin≤1:=hp.trans hp1
  have hpowp:pmin^h≤p^S.card:=
    (pow_le_pow_of_le_one hpmin.le hpmin1 hS).trans (pow_le_pow_left₀ hpmin.le hp _)
  have hpowS:smin^h≤smin^J.card:=pow_le_pow_of_le_one hsmin.le hsmin1 hJ
  have hprod:smin^J.card≤∏ u∈J,s u j:=by
    rw [←Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _=>hsmin.le) (fun u _=>hs u)
  exact mul_le_mul hpowp (hpowS.trans hprod) (pow_nonneg hsmin.le _) (pow_nonneg (hpmin.le.trans hp) _)
end Oberwolfach
