module

public import Oberwolfach.FractionalRelabeling
public import Oberwolfach.CycleFractionalThreshold

@[expose] public section

/-! Fractional decompositions on small vertex sets, interpreted on the
original vertex set without identifying different physical subgraphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem HasFractionalDecomposition.map_embedding {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {P : SimpleGraph V → Prop}
    (h : HasFractionalDecomposition G P) (f : V ↪ W) :
    HasFractionalDecomposition (G.map f)
      (fun K => ∃ H,P H ∧ K=H.map f) := by
  obtain ⟨w,hw,hs,he⟩ := h
  apply fractionalDecomposition_of_indexed _ _ (fun H => H.map f) w hw
  · intro H hH
    exact ⟨SimpleGraph.map_monotone _ (hs H hH).1,H,(hs H hH).2,rfl⟩
  · intro u v
    by_cases hu : u∈Set.range f
    · obtain ⟨a,rfl⟩ := hu
      by_cases hv : v∈Set.range f
      · obtain ⟨b,rfl⟩ := hv
        simp_rw [SimpleGraph.map_adj_apply]
        exact he a b
      · have hn (H : SimpleGraph V) : ¬(H.map f).Adj (f a) v := by
          intro hadj
          rw [SimpleGraph.map_adj] at hadj
          obtain ⟨x,y,hxy,hx,hy⟩ := hadj
          exact hv ⟨y,hy⟩
        simp only [if_neg (hn _),Finset.sum_const_zero]
    · have hn (H : SimpleGraph V) : ¬(H.map f).Adj u v := by
        intro hadj
        rw [SimpleGraph.map_adj] at hadj
        obtain ⟨x,y,hxy,hx,hy⟩ := hadj
        exact hu ⟨x,hx⟩
      simp only [if_neg (hn _),Finset.sum_const_zero]

theorem HasFractionalDecomposition.map_embedded_cycles {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {r : ℕ}
    (h : HasFractionalDecomposition G (fun H => IsEmbeddedCycle H r)) (f : V ↪ W) :
    HasFractionalDecomposition (G.map f) (fun H => IsEmbeddedCycle H r) :=
  (h.map_embedding f).mono_property (by
    rintro K ⟨H,hH,rfl⟩
    exact hH.map f)

theorem cycle_fractional_positive_margin_finite (r : ℕ) (hr : 3≤r)
    (α : ℝ) (hα : 0<α) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ G : SimpleGraph V,
      (∀ v,(cycleThreshold r+α)*Fintype.card V≤(G.degree v:ℝ)) →
      HasFractionalDecomposition G (fun H => IsEmbeddedCycle H r) := by
  obtain ⟨N,hN⟩ := cycle_fractional_positive_margin r hr α hα
  refine ⟨N,?_⟩
  intro V _ _ hn G hdeg
  let e := Fintype.equivFin V
  have hg : HasFractionalDecomposition (G.map e.toEmbedding)
      (fun H => IsEmbeddedCycle H r) := by
    apply hN _ hn
    intro i
    obtain ⟨v,rfl⟩ := e.surjective i
    have hd := SimpleGraph.degree_map_apply G e.toEmbedding v
    have hh := hdeg v
    simp only [← SimpleGraph.ncard_neighborSet] at hd hh ⊢
    have hd' : ((G.map e.toEmbedding).neighborSet (e v)).ncard=(G.neighborSet v).ncard := by
      simpa only [Equiv.coe_toEmbedding] using hd
    rw [hd']
    exact hh
  have hh := hg.map_cycles e.symm
  have he : (G.map e.toEmbedding).map e.symm.toEmbedding=G := by
    rw [SimpleGraph.map_map]
    have hid : (⇑e.symm.toEmbedding ∘ ⇑e.toEmbedding)=id := by
      funext v
      exact e.symm_apply_apply v
    rw [hid,SimpleGraph.map_id]
  rwa [he] at hh

end Oberwolfach
