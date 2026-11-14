module

public import Oberwolfach.FloorOrbit

@[expose] public section

/-! First stopping time and terminal sizes for the vertex-set recursion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem floorOrbit_stopping {ε : ℝ} (he : 0 < ε) (he1 : ε < 1)
    {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) (hlarge : 2 ≤ ε * m) :
    ∃ ℓ : ℕ, 0 < ℓ ∧ floorOrbit ε n ℓ < m ∧
      (∀ i < ℓ, m ≤ floorOrbit ε n i) ∧
      (∀ i ≤ ℓ, ε * m / 2 ≤ (floorOrbit ε n i : ℝ)) := by
  have hex : ∃ i : ℕ, floorOrbit ε n i < m :=
    ⟨n, by rw [floorOrbit_eventually_zero he1]; exact hm⟩
  let ℓ := Nat.find hex
  have hlast : floorOrbit ε n ℓ < m := Nat.find_spec hex
  have hbefore : ∀ i < ℓ, m ≤ floorOrbit ε n i := by
    intro i hi
    exact Nat.le_of_not_gt (Nat.find_min hex hi)
  have hlpos : 0 < ℓ := by
    by_contra hh
    have hz : ℓ = 0 := by omega
    rw [hz, floorOrbit_zero] at hlast
    omega
  have hprev := hbefore (ℓ - 1) (by omega)
  have hprevReal : (m : ℝ) ≤ floorOrbit ε n (ℓ - 1) := by exact_mod_cast hprev
  have hmstep := mul_le_mul_of_nonneg_left hprevReal he.le
  have hsuc : ℓ - 1 + 1 = ℓ := by omega
  have hround := Nat.lt_floor_add_one (ε * (floorOrbit ε n (ℓ - 1) : ℝ))
  rw [← floorOrbit_succ, hsuc] at hround
  have hterm : ε * m / 2 ≤ (floorOrbit ε n ℓ : ℝ) := by linarith
  refine ⟨ℓ, hlpos, hlast, hbefore, ?_⟩
  intro i hi
  have hh : floorOrbit ε n ℓ ≤ floorOrbit ε n i := floorOrbit_antitone he1 n hi
  exact hterm.trans (by exact_mod_cast hh)

end Oberwolfach
