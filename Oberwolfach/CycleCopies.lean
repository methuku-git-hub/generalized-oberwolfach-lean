module

public import Oberwolfach.Definitions
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

@[expose] public section

/-! The manuscript's cycle-copy encoding agrees with mathlib's actual cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycleGraph_modular_adj {r : ℕ} (hr : 2 ≤ r) (i j : Fin r) :
    (SimpleGraph.cycleGraph r).Adj i j ↔
      (i.val + 1) % r = j.val ∨ (j.val + 1) % r = i.val := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hr
  have hr' : r = k + 2 := by omega
  clear hk
  subst r
  rw [SimpleGraph.cycleGraph_adj]
  simp only [sub_eq_iff_eq_add, Fin.ext_iff, Fin.val_add, Fin.val_one, Nat.add_comm]
  omega

theorem isCycleCopy_iff_map {n r : ℕ} (H : SimpleGraph (Fin n)) :
    IsCycleCopy H r ↔ 3 ≤ r ∧
      ∃ f : Fin r ↪ Fin n, H = (SimpleGraph.cycleGraph r).map f := by
  constructor
  · rintro ⟨hr, f, hf⟩
    refine ⟨hr, f, ?_⟩
    ext u v
    rw [hf, SimpleGraph.map_adj]
    simp only [cycleGraph_modular_adj (by omega : 2 ≤ r)]
    constructor
    · rintro ⟨i, j, hi, hj, hij⟩
      exact ⟨i, j, hij, hi, hj⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      exact ⟨i, j, hi, hj, hij⟩
  · rintro ⟨hr, f, rfl⟩
    refine ⟨hr, f, ?_⟩
    intro u v
    rw [SimpleGraph.map_adj]
    simp only [cycleGraph_modular_adj (by omega : 2 ≤ r)]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      exact ⟨i, j, hi, hj, hij⟩
    · rintro ⟨i, j, hi, hj, hij⟩
      exact ⟨i, j, hij, hi, hj⟩

theorem cycleGraph_regular {r : ℕ} (hr : 3 ≤ r) :
    (SimpleGraph.cycleGraph r).IsRegularOfDegree 2 := by
  have heq : r = (r - 3) + 3 := by omega
  rw [heq]
  intro x
  exact SimpleGraph.cycleGraph_degree_three_le

theorem cycleGraph_edge_card {r : ℕ} (hr : 3 ≤ r) :
    (SimpleGraph.cycleGraph r).edgeFinset.card = r := by
  have hh := (SimpleGraph.cycleGraph r).sum_degrees_eq_twice_card_edges
  have hreg : ∀ v, (SimpleGraph.cycleGraph r).degree v = 2 := cycleGraph_regular hr
  simp only [hreg, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hh
  omega

theorem IsCycleCopy.edge_card {n r : ℕ} {H : SimpleGraph (Fin n)}
    (hH : IsCycleCopy H r) : H.edgeFinset.card = r := by
  obtain ⟨hr, f, rfl⟩ := (isCycleCopy_iff_map H).mp hH
  have hh := SimpleGraph.card_edgeFinset_map f (SimpleGraph.cycleGraph r)
  have hh' : ((SimpleGraph.cycleGraph r).map f).edgeFinset.card =
      (SimpleGraph.cycleGraph r).edgeFinset.card := by
    simpa only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset] using hh
  simpa only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    using hh'.trans (cycleGraph_edge_card hr)

theorem IsCycleCopy.not_bipartite {n r : ℕ} {H : SimpleGraph (Fin n)}
    (hH : IsCycleCopy H r) (hr : Odd r) : ¬ H.IsBipartite := by
  obtain ⟨hthree, f, hf⟩ := (isCycleCopy_iff_map H).mp hH
  intro hb
  let g : SimpleGraph.cycleGraph r →g H := {
    toFun := f
    map_rel' := by
      intro u v huv
      rw [hf]
      exact SimpleGraph.map_adj_apply.mpr huv }
  have hh := (hb.of_hom g).chromaticNumber_le
  rw [SimpleGraph.chromaticNumber_cycleGraph_of_odd r (by omega) hr] at hh
  norm_num at hh

end Oberwolfach
