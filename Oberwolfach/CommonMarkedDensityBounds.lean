module

public import Oberwolfach.MarkedSeedDensities
public import Oberwolfach.SuccessorCyclicMargin

@[expose] public section

/-! Uniform common-class density bounds and the large even-length degree
margin. No sampled density or retained degree replaces a supplied centre. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Oberwolfach

theorem successorCycleRatio_formula (k : ℕ) :
    successorCycleRatio k=1/2+1/(4*(k:ℝ)+6) := by
  unfold successorCycleRatio
  have hd : (2*((k:ℝ)+2)-1)≠0 := by linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hd' : 4*(k:ℝ)+6≠0 := by positivity
  field_simp
  <;> ring

theorem successorCycleRatio_eventually_margin (α : ℝ) (hα : 0<α) :
    ∃ K : ℕ,∀ k : ℕ,K≤k → successorCycleRatio k+α/2≤1/2+α := by
  refine ⟨Nat.ceil (1/α),?_⟩
  intro k hk
  have hceil : 1/α≤(k:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  have hprod : 1≤(k:ℝ)*α := (div_le_iff₀ hα).mp hceil
  rw [successorCycleRatio_formula]
  have hdiv : 1/(4*(k:ℝ)+6)≤α/2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<4*(k:ℝ)+6)).mpr
    nlinarith
  linarith

theorem marked_common_density_bounds (m : ℕ) (hm : 1≤m)
    (ρ s ρstar sstar : ℝ) (hρstar : 0<ρstar) (hsstar : 0<sstar)
    (hρlo : ρstar≤ρ) (hρhi : ρ≤1) (hslo : sstar≤s) (hshi : s≤1/100) :
    let p := ρ*s/2
    let k := p/m
    let pstar := min (ρstar*sstar/(2*m)) (sstar*sstar/m)
    let astar := (sstar/m)*(sstar/m)
    0<pstar ∧ 0<astar ∧ pstar≤p ∧ pstar≤k ∧ pstar≤s*s/m ∧ s*s/m≤1 ∧
      astar≤(s/m)*(s/m) ∧ astar≤s*s/m ∧ 0<p ∧ 0<k ∧ 2*p+2*k≤1 := by
  intro p k pstar astar
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hs0 : 0<s := hsstar.trans_le hslo
  have hρ0 : 0<ρ := hρstar.trans_le hρlo
  obtain ⟨hbase,hp,hk,hs,hp1,hk1,hs1,ht,hphys⟩ :=
    marked_seed_density_bounds m hm ρ s ρstar sstar hρstar hsstar hρlo hρhi hslo hshi
  have hpstar : 0<pstar := by dsimp [pstar];positivity
  have ha : 0<astar := by dsimp [astar];positivity
  have hsprod : sstar*sstar≤s*s := mul_le_mul hslo hslo hsstar.le hs0.le
  have hsbar : sstar*sstar/m≤s*s/m := div_le_div_of_nonneg_right hsprod hm0.le
  have hsq : (s/m)*(s/m)≤s*s/m := by
    have hdiv : s/m≤s := by apply (div_le_iff₀ hm0).mpr;nlinarith
    calc
      _ ≤ s*(s/m) := mul_le_mul_of_nonneg_right hdiv (by positivity)
      _ = _ := by ring
  have haraw : astar≤(s/m)*(s/m) := by
    dsimp [astar]
    have hh := div_le_div_of_nonneg_right hslo hm0.le
    exact mul_le_mul hh hh (by positivity) (by positivity)
  have hupper : s*s/m≤1 := by
    apply (div_le_iff₀ hm0).mpr
    nlinarith
  exact ⟨hpstar,ha,(min_le_left _ _).trans hp,(min_le_left _ _).trans hk,
    (min_le_right _ _).trans hsbar,hupper,haraw,haraw.trans hsq,
    hbase.trans_le hp,hbase.trans_le hk,hphys⟩

theorem marked_common_start_mass (m : ℕ) (hm : 1≤m) (ω sstar s n u : ℝ)
    (hω : 0<ω) (hsstar : 0<sstar) (hslo : sstar≤s) (hn : 0≤n) (hu : ω*n≤u) :
    (ω*sstar/(2*m))*n≤(s/m)*u := by
  have hm0 : (0:ℝ)<m := by exact_mod_cast (lt_of_lt_of_le (by omega : 0<1) hm)
  have hs0 : 0<s := hsstar.trans_le hslo
  have hmul := mul_le_mul_of_nonneg_left hu (div_nonneg hs0.le hm0.le)
  have hss := mul_le_mul_of_nonneg_right hslo (mul_nonneg hω.le hn)
  have hnum : ω*sstar*n≤2*s*ω*n := by
    nlinarith only [hss,mul_nonneg hs0.le (mul_nonneg hω.le hn)]
  have hcalc : (ω*sstar/(2*m))*n≤(s/m)*(ω*n) := by
    calc
      _ = (ω*sstar*n)/(2*m) := by ring
      _ ≤ (2*s*ω*n)/(2*m) := div_le_div_of_nonneg_right hnum (by positivity)
      _ = _ := by field_simp <;> ring
  exact hcalc.trans hmul

end Oberwolfach
