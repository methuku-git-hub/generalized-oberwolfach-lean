module

public import Oberwolfach.MarkedWheelFamilyLoads
public import Oberwolfach.MarkedPackingRimGraphs

@[expose] public section

/-! Disjointness from a previous row-wheel family. Free physical rims are
deleted; the prescribed root rims are checked separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I : Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {H₀ HK : V → U → Prop}
    {π : Equiv.Perm V} {b m : ℕ}

theorem marked_free_rim_extension_disjoint (hm : 1≤m) (hb : 1≤b)
    (C : I → MarkedWheel tail head ktail khead m π b H₀ HK)
    (W : MarkedWheel tail head ktail khead m π b H₀ HK)
    (X : Finset V) (T : I → Finset (Finset V)) (T' : Finset (Finset V))
    (hold : ∀ i e, e∈markedCyclePhysicalEdges tail head ktail khead m π b (C i).1 → e⊆X ∨ e∈T i)
    (hnew : ∀ e, e∈markedCyclePhysicalEdges tail head ktail khead m π b W.1 → e⊆X ∨ e∈T')
    (houtside : ∀ i e, e∈T i → ¬e⊆X)
    (hroots : ∀ i, Disjoint (T i) T')
    (hhubs : ∀ i, (C i).2.val≠W.2.val)
    (hD : Disjoint (markedWheelRimGraph W) (spanningRestriction (markedFamilyRim C) X)) :
    ∀ i, Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources W) := by
  intro i
  apply Finset.disjoint_left.mpr
  intro e he hw
  cases e with
  | inr e =>
    have hc := (markedWheelPhysicalResources_spoke (C i) e.1 e.2).mp he
    have hn := (markedWheelPhysicalResources_spoke W e.1 e.2).mp hw
    exact hhubs i (hc.1.trans hn.1.symm)
  | inl e =>
    rw [markedWheelPhysicalResources_rim] at he hw
    rcases hold i e he with hx|ht
    · have hcard : e.card=2 := by
        obtain ⟨a,ha,h⟩ := Finset.mem_image.mp he
        rw [←h]
        exact markedCycle_physical_edge_card tail head ktail khead m π b hm hb (C i).1 a
      obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hcard
      have hd : (spanningRestriction (markedFamilyRim C) X).Adj x y :=
        (spanningRestriction_adj _ _ _ _).mpr
          ⟨SimpleGraph.iSup_adj.mpr ⟨i,hxy,he⟩,hx (by simp),hx (by simp)⟩
      exact disjoint_graphs_no_common_edge _ _ hD x y ⟨hxy,hw⟩ hd
    · rcases hnew e hw with hx|ht'
      · exact houtside i e ht hx
      · exact Finset.disjoint_left.mp (hroots i) ht ht'

end Oberwolfach
