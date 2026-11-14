module

public import Oberwolfach.LongPreparationPhysicalContainment

@[expose] public section
/-! Required edges avoid an old packing when used orientations are recorded. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_required_graph_avoids_used_packing
    {V:Type} [Fintype V] [DecidableEq V]
    (P P₀ Sel Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (D:V→V→Prop) (Pack:Finset (Sym2 V))
    (hP₀:P₀≤P\Used) (hPack:Pack⊆Used.edgeFinset):
    Disjoint (longRequiredPhysicalGraph P P₀ Sel π d I D (fun x y=>Used.Adj x y)).edgeFinset Pack:=by
  apply Finset.disjoint_left.mpr
  intro e he hp
  induction e using Sym2.ind with
  | _ x y =>
    have hu:Used.Adj x y:=by
      have hh:=hPack hp
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hh
    have hk:(longRequiredPhysicalGraph P P₀ Sel π d I D (fun x y=>Used.Adj x y)).Adj x y:=by
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he
    change (spanningRestriction (P₀\Sel) I ⊔ longCloseRequiredGraph P π d D (fun x y=>Used.Adj x y)).Adj x y at hk
    simp only [SimpleGraph.sup_adj] at hk
    rcases hk with ha|ha
    · have hP: P₀.Adj x y:=((spanningRestriction_adj _ _ _ _).mp ha).1.1
      exact (hP₀ hP).2 hu
    · change P.Adj x y ∧ PermutationClose π (3*d) x y ∧
        ((D x y ∧ ¬Used.Adj x y) ∨ (D y x ∧ ¬Used.Adj y x)) at ha
      rcases ha.2.2 with hh|hh
      · exact hh.2 hu
      · exact hh.2 hu.symm
end Oberwolfach
