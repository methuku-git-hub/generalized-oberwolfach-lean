module

public import Oberwolfach.FactorDirectedCycleChain
public import Oberwolfach.FactorDirectedEdgesToPhysical

@[expose] public section
/-! Orient the actual two-factor components as valid source cycle pieces. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_components_as_directed_pieces (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2):
    ∃ (root:F.ConnectedComponent→V) (tail:F.ConnectedComponent→List V)
      (D:V→V→Prop),
      (∀ c,(PrescribedSourcePiece.cycle (root c) (tail c)).Valid D ⊥) ∧
      (∀ c x,x∈root c::tail c ↔ x∈c.supp) ∧
      (∀ c c' x,x∈root c::tail c→x∈root c'::tail c'→c=c') ∧
      (∀ x,∃ c,x∈root c::tail c) ∧
      (∀ x y,D x y→F.Adj x y) ∧
      (∀ x y,F.Adj x y ↔ ∃ c,x∈root c::tail c ∧
        s(x,y)∈(PrescribedSourcePiece.cycle (root c) (tail c)).edges) := by
  obtain ⟨root,tail,hcycle,hverts,hdisj,hcover,hedges⟩:=two_factor_all_components_enumerated F hF
  let D:V→V→Prop := fun x y=>∃ c,(x,y)∈prescribedDirectedPathEdges ((root c::tail c)++[root c])
  refine ⟨root,tail,D,?_,hverts,hdisj,hcover,?_,?_⟩
  · intro c
    change (root c::tail c).Nodup ∧ 3≤(root c::tail c).length ∧
      DirectedCycleThrough D ⊥ (root c::tail c)
    refine ⟨(hcycle c).1,(hcycle c).2,?_⟩
    apply (directed_cycle_through_iff_chain D ⊥ (root c) (tail c)).2
    apply (prescribed_directed_edges_chain (fun x y=>D x y ∧ ¬(⊥:SimpleGraph V).Adj x y) _).2
    intro e he
    refine ⟨⟨c,he⟩,?_⟩
    simp
  · intro x y hxy
    obtain ⟨c,hc⟩:=hxy
    have hend:=prescribed_directed_path_edge_endpoints ((root c::tail c)++[root c]) (x,y) hc
    have hx:x∈root c::tail c := by simpa [or_assoc,or_left_comm,or_comm] using hend.1
    exact (hedges x y).2 ⟨c,hx,directed_path_edge_is_physical _ x y hc⟩
  · intro x y
    simpa [PrescribedSourcePiece.edges] using hedges x y
end Oberwolfach
