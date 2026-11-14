module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! The two floor recursions used for vortex vertex and index sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

def floorOrbit (ε : ℝ) (n : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => Nat.floor (ε * floorOrbit ε n i)

theorem floorOrbit_zero (ε : ℝ) (n : ℕ) : floorOrbit ε n 0 = n := rfl

theorem floorOrbit_succ (ε : ℝ) (n i : ℕ) :
    floorOrbit ε n (i + 1) = Nat.floor (ε * floorOrbit ε n i) := rfl

theorem floor_step_lt {ε : ℝ} (he1 : ε < 1) {n : ℕ} (hn : 0 < n) :
    Nat.floor (ε * n) < n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  apply (Nat.floor_lt' hn.ne').mpr
  nlinarith

theorem floorOrbit_le_sub {ε : ℝ} (he1 : ε < 1) (n i : ℕ) :
    floorOrbit ε n i ≤ n - i := by
  induction i with
  | zero => simp [floorOrbit]
  | succ i ih =>
    rw [floorOrbit_succ]
    by_cases hz : floorOrbit ε n i = 0
    · simp [hz]
    · have hs := floor_step_lt he1 (Nat.pos_of_ne_zero hz)
      omega

theorem floorOrbit_eventually_zero {ε : ℝ} (he1 : ε < 1) (n : ℕ) :
    floorOrbit ε n n = 0 := by
  have hh := floorOrbit_le_sub he1 n n
  omega

theorem floorOrbit_shrinks {ε : ℝ} (he : 0 ≤ ε) (n i : ℕ) :
    (floorOrbit ε n (i + 1) : ℝ) ≤ ε * floorOrbit ε n i := by
  rw [floorOrbit_succ]
  exact Nat.floor_le (by positivity)

theorem floorOrbit_antitone {ε : ℝ} (he1 : ε < 1) (n : ℕ) :
    Antitone (floorOrbit ε n) := by
  apply antitone_nat_of_succ_le
  intro i
  rw [floorOrbit_succ]
  by_cases hz : floorOrbit ε n i = 0
  · simp [hz]
  · exact (floor_step_lt he1 (Nat.pos_of_ne_zero hz)).le

theorem floorOrbit_rounding_error {ε a : ℝ} (he : 0 ≤ ε) (he1 : ε < 1)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) {n u : ℕ} (hinit : (u : ℝ) = a * n) (i : ℕ) :
    |(floorOrbit ε u i : ℝ) - a * floorOrbit ε n i| < 1 / (1 - ε) := by
  have hden : 0 < 1 - ε := by linarith
  induction i with
  | zero => simp only [floorOrbit_zero, hinit, sub_self, abs_zero]; positivity
  | succ i ih =>
    let x : ℝ := floorOrbit ε n i
    let y : ℝ := floorOrbit ε u i
    let r : ℝ := ε * x - Nat.floor (ε * x)
    let s : ℝ := ε * y - Nat.floor (ε * y)
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hy : 0 ≤ y := by dsimp [y]; positivity
    have hr0 : 0 ≤ r := sub_nonneg.mpr (Nat.floor_le (mul_nonneg he hx))
    have hr1 : r < 1 := by have hh := Nat.lt_floor_add_one (ε * x); dsimp [r]; linarith
    have hs0 : 0 ≤ s := sub_nonneg.mpr (Nat.floor_le (mul_nonneg he hy))
    have hs1 : s < 1 := by have hh := Nat.lt_floor_add_one (ε * y); dsimp [s]; linarith
    have habs : |a * r - s| < 1 := by
      apply abs_lt.mpr
      constructor
      · nlinarith [mul_nonneg ha hr0]
      · have hh := mul_le_mul_of_nonneg_right ha1 hr0
        nlinarith
    have hrec : ((Nat.floor (ε * y) : ℕ) : ℝ) - a * Nat.floor (ε * x) =
        ε * (y - a * x) + (a * r - s) := by dsimp [r, s]; ring
    rw [floorOrbit_succ, floorOrbit_succ]
    change |(Nat.floor (ε * y) : ℝ) - a * Nat.floor (ε * x)| < _
    rw [hrec]
    calc
      _ ≤ |ε * (y - a * x)| + |a * r - s| := abs_add_le _ _
      _ = ε * |y - a * x| + |a * r - s| := by rw [abs_mul, abs_of_nonneg he]
      _ < ε * (1 / (1 - ε)) + 1 :=
        add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left ih.le he) habs
      _ = _ := by field_simp; ring

end Oberwolfach
