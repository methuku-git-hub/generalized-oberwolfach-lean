module

public import Oberwolfach.CyclicWeightData
public import Oberwolfach.CyclicSectorFormula
public import Oberwolfach.SectorBounds
public import Oberwolfach.IntervalPositive
public import Oberwolfach.InterfaceScaleBounds

@[expose] public section

/-! Pointwise estimates for the exact weights chosen by the cyclic
fixed-point construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cyclicSectorWeight_formula {k : ℕ} {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X]
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop)
    (Q : transportProduct (cyclicInterfaceMarginal L) (finRotate (k + 2)))
    (hm : ∀ i x, 0 < cyclicInterfaceMarginal L i x)
    (hH : ∀ i x z, 0 < cyclicResidualSystem L R Q i x z)
    (hfixed : ∀ i x z, Q.val i x z = walkTransport (cyclicInterfaceMarginal L)
      (cyclicResidualSystem L R Q) (finRotate (k + 2))
      (finRotate (k + 2) i) (k + 1) z x)
    (p : Fin (k + 2) → X × Y × X)
    (hc : ∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1)
    (hp : ∀ i, L i (p i).1 (p i).2.1 ∧ R i (p i).2.1 (p i).2.2)
    (c : Fin (k + 2)) :
    cyclicSectorWeight L R Q c p =
      (∏ i ∈ Finset.univ.erase c, cyclicResidualPath L R Q i (p i)) /
        ((intervalCommon (L c) (R c) (p c).1 (p c).2.2 : ℝ) *
          ∏ j ∈ (Finset.univ.erase c).erase (finRotate (k + 2) c),
            cyclicInterfaceMarginal L j (p j).1) := by
  have hC : 0 < (intervalCommon (L c) (R c) (p c).1 (p c).2.2 : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨(p c).2.1, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hp c⟩⟩
  have hh := cyclic_sector_formula (cyclicInterfaceMarginal L)
    (cyclicResidualSystem L R Q) hm hH c (Q.val c) (hfixed c)
    (fun i => (p i).1)
    (fun i => if i = c then cyclicReservePath L R Q i (p i)
      else cyclicResidualPath L R Q i (p i))
    (fun i => cyclicResidualPath L R Q i (p i))
    (intervalCommon (L c) (R c) (p c).1 (p c).2.2) hC
    (by
      simp only [ite_true, cyclicReservePath, endpointReserve]
      rw [if_pos (hp c), hc c])
    (by intro i hi; simp only [hi, ite_false])
  simpa only [cyclicSectorWeight, hc] using hh


def cyclicSectorLower (k : ℕ) (α : ℝ) : ℝ :=
  ((((2 * (k + 2) - 1) * α / (k + 2)) ^ 2 / (k + 1)) ^ (k + 1)) /
    ((1 / (k + 2)) ^ k)

def cyclicSectorUpper (k : ℕ) (α : ℝ) : ℝ :=
  ((1 / ((k + 1) * ((2 * (k + 2) - 1) * α / (k + 2)) *
    ((k + 2) / (2 * (k + 2) - 1)))) ^ (k + 1)) /
    ((1 / (2 * (k + 2) - 1)) * (1 / (2 * (k + 2) - 1)) ^ k)

theorem cyclicSectorConstants_pos (k : ℕ) (α : ℝ) (hα : 0 < α) :
    0 < cyclicSectorLower k α ∧ 0 < cyclicSectorUpper k α := by
  have hfac : (0 : ℝ) < 2 * (k + 2) - 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  unfold cyclicSectorLower cyclicSectorUpper
  constructor <;> positivity

set_option maxHeartbeats 800000 in
theorem cyclicSectorWeight_bounds {k : ℕ} {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X]
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop)
    (δ α : ℝ) (hn : 0 < Fintype.card Y) (hα : 0 < α)
    (hcard : Fintype.card X = Fintype.card Y)
    (ht : ((k + 2) + (2 * (k + 2) - 1) * α) * Fintype.card Y ≤
      (2 * (k + 2) - 1) * δ)
    (hdL : ∀ i x, δ ≤ (Finset.univ.filter (L i x)).card)
    (hdY : ∀ i y, δ ≤ (Finset.univ.filter (fun x => L i x y)).card)
    (hY : ∀ i y, (Finset.univ.filter (fun x => L i x y)).card =
      (Finset.univ.filter (R i y)).card)
    (hX : ∀ i z, (Finset.univ.filter (fun y => R i y z)).card =
      (Finset.univ.filter (L (finRotate (k + 2) i) z)).card)
    (Q : transportProduct (cyclicInterfaceMarginal L) (finRotate (k + 2)))
    (hfixed : ∀ i x z, Q.val i x z = walkTransport (cyclicInterfaceMarginal L)
      (cyclicResidualSystem L R Q) (finRotate (k + 2))
      (finRotate (k + 2) i) (k + 1) z x)
    (p : Fin (k + 2) → X × Y × X)
    (hc : ∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1)
    (hp : ∀ i, L i (p i).1 (p i).2.1 ∧ R i (p i).2.1 (p i).2.2)
    (c : Fin (k + 2)) :
    cyclicSectorLower k α / (Fintype.card Y : ℝ) ^ (2 * k + 2) ≤
        cyclicSectorWeight L R Q c p ∧
    cyclicSectorWeight L R Q c p ≤
      cyclicSectorUpper k α / (Fintype.card Y : ℝ) ^ (2 * k + 2) := by
  have hq : (2 : ℝ) ≤ k + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hn' : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hn
  obtain ⟨hδ, hbase⟩ := positive_margin_base hq hn' hα ht
  have hdR (i : Fin (k + 2)) (z : X) :
      δ ≤ (Finset.univ.filter (fun y => R i y z)).card := by
    rw [hX i z]; exact hdL _ z
  have hQmat (i : Fin (k + 2)) : Q.val i ∈ transportMatrices
      (fun x => (Finset.univ.filter (L i x)).card / (k + 2 : ℝ))
      (fun z => (Finset.univ.filter (fun y => R i y z)).card / (k + 2 : ℝ)) := by
    have hh := Q.property i (Set.mem_univ i)
    change Q.val i ∈ transportMatrices
      (fun x => cyclicInterfaceDegree L i x / (k + 2 : ℝ))
      (fun z => cyclicInterfaceDegree L (finRotate (k + 2) i) z / (k + 2 : ℝ)) at hh
    simpa only [hX, cyclicInterfaceDegree] using hh
  have hm (i : Fin (k + 2)) (x : X) : 0 < cyclicInterfaceMarginal L i x :=
    div_pos (lt_of_lt_of_le hδ (hdL i x)) (by positivity)
  have hH (i : Fin (k + 2)) (x z : X) : 0 < cyclicResidualSystem L R Q i x z :=
    intervalResidualMap_pos (L i) (R i) (Q.val i) (k + 2) δ α hq hn hα hcard
      ht (hdL i) (hdR i) (hdY i) (hY i) (hQmat i) x z
  rw [cyclicSectorWeight_formula L R Q hm hH hfixed p hc hp c]
  let σ : ℝ := (2 * (k + 2) - 1) * α / (k + 2)
  let rlo : ℝ := σ ^ 2 / (k + 1)
  let rhi : ℝ := 1 / ((k + 1) * σ * ((k + 2) / (2 * (k + 2) - 1)))
  let d : ℝ := 1 / (2 * (k + 2) - 1)
  have hfac : (0 : ℝ) < 2 * (k + 2) - 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hlo : 0 < rlo := by dsimp only [rlo]; positivity
  have hhi : 0 < rhi := by dsimp only [rhi]; positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  have hpath (i : Fin (k + 2)) : rlo / Fintype.card Y ≤ cyclicResidualPath L R Q i (p i) ∧
      cyclicResidualPath L R Q i (p i) ≤ rhi / Fintype.card Y := by
    have hh := interval_residual_path_two_sided (L i) (R i) (Q.val i) (k + 2) δ α
      hq hn hα hcard ht (hdL i) (hdR i) (hdY i) (hQmat i)
      (p i).1 (p i).2.1 (p i).2.2 (hp i).1 (hp i).2
    dsimp only at hh
    have hkm : (k + 2 : ℝ) - 1 = k + 1 := by ring
    rw [hkm] at hh
    simpa only [cyclicResidualPath, rlo, rhi, σ, div_div, mul_assoc] using hh
  have hdegree (i : Fin (k + 2)) : d * Fintype.card Y ≤ cyclicInterfaceMarginal L i (p i).1 ∧
      cyclicInterfaceMarginal L i (p i).1 ≤ (1 / (k + 2 : ℝ)) * Fintype.card Y :=
    degree_marginal_scale hq hn' hbase (hdL i (p i).1)
      (by
        change ((Finset.univ.filter (L i (p i).1)).card : ℝ) ≤ Fintype.card Y
        exact_mod_cast Finset.card_le_univ (Finset.univ.filter (L i (p i).1)))
  have hcommon := intervalCommon_scale (L c) (R c) (k + 2) δ hq hbase (hdL c) (hdR c)
    (p c).1 (p c).2.2
  have hbound := product_ratio_bounds (Finset.univ.erase c)
    ((Finset.univ.erase c).erase (finRotate (k + 2) c))
    (fun i => cyclicResidualPath L R Q i (p i))
    (fun j => cyclicInterfaceMarginal L j (p j).1)
    (Fintype.card Y) rlo rhi d 1 d (1 / (k + 2))
    (intervalCommon (L c) (R c) (p c).1 (p c).2.2)
    hn' hlo hhi hd (by norm_num) hd (by positivity)
    (fun i _ => hpath i) (fun i _ => hdegree i) hcommon
  have hne : finRotate (k + 2) c ≠ c := by
    simpa only [Fin.castSucc_zero, cyclicChainOrder_zero] using
      cyclicChainOrder_cast_ne c (0 : Fin (k + 1))
  have hcard1 : (Finset.univ.erase c).card = k + 1 := by simp
  have hcard2 : ((Finset.univ.erase c).erase (finRotate (k + 2) c)).card = k := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩), hcard1]
    omega
  simpa only [hcard1, hcard2, show k + 1 + k + 1 = 2 * k + 2 by omega,
    rlo, rhi, σ, d, one_mul, cyclicSectorLower, cyclicSectorUpper] using hbound

end Oberwolfach
