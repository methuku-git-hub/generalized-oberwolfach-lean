module

public import Oberwolfach.MarkedTwoStageDensityBounds

@[expose] public section
/-! The canonical lower bound also satisfies the weighted-load theorem's
upper bounds for the same fixed density profile. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem marked_two_stage_complete_density_bounds
    (r:ℕ) (t rho:ℝ) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1)
    (hst:(((r+1)+3:ℕ):ℝ)*t≤1):
    let pstar:=rho*t/2
    let p:=rho*((((r+1)+3:ℕ):ℝ)*t)/2
    let k:=rho*t/2
    let s:=(((r+1)+3:ℕ):ℝ)*t;
    0<pstar∧pstar≤p∧pstar≤k∧pstar≤s∧p≤1∧k≤1∧s≤1:=by
  intro pstar p k s
  have hb:=marked_two_stage_density_lower_bounds r t rho ht hrho hrho1 hst
  have hn:0≤(((r+1)+3:ℕ):ℝ):=Nat.cast_nonneg _
  have hsn:0≤s:=mul_nonneg hn ht.le
  have hρs:rho*s≤s:=by nlinarith [mul_nonneg (sub_nonneg.mpr hrho1) hsn]
  refine ⟨hb.1,hb.2.2.1,le_refl _,hb.2.2.2.2,?_,hb.2.1,hst⟩
  dsimp only [p,s] at *
  nlinarith
end Oberwolfach
