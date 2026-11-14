module

public import Oberwolfach.OrdinaryBoundaryGraph
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
/-! A boundary at a deeper nested pair lies either inside the present pair
or across its boundary.  This turns separately controlled costs into a
uniform bound at the deeper boundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nested_boundary_degree (Q R:SimpleGraph V) (H S:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (hTX:T⊆X) (hWZ:W⊆Z)
    (hR:R≤Q) (hS:∀v u,S v u→H v u) (a b:ℝ)
    (hinner:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)).degree w:ℝ)≤a)
    (houter:∀w:V⊕U,((ordinaryBoundaryGraph Q H X Z).degree w:ℝ)≤b):
    ∀w:V⊕U,((ordinaryBoundaryGraph R S T W).degree w:ℝ)≤a+b:=by
  let Ω:=ordinaryInnerVertices X Z
  let Ωdeep:=ordinaryInnerVertices T W
  have hnested:Ωdeep⊆Ω:=by
    intro x hx
    cases x with
    | inl v=>exact (ordinaryInnerVertices_left X Z v).mpr (hTX ((ordinaryInnerVertices_left T W v).mp hx))
    | inr u=>exact (ordinaryInnerVertices_right X Z u).mpr (hWZ ((ordinaryInnerVertices_right T W u).mp hx))
  have hphys:ordinaryPhysicalGraph R S≤ordinaryPhysicalGraph Q H:=by
    intro x y hxy
    cases x with
    | inl v=>cases y with
      | inl w=>exact hR hxy
      | inr u=>exact hS v u hxy
    | inr u=>cases y with
      | inl v=>exact hS v u hxy
      | inr z=>exact hxy.elim
  have hsub:ordinaryBoundaryGraph R S T W≤spanningRestriction (ordinaryPhysicalGraph R S) Ω⊔
      ordinaryBoundaryGraph Q H X Z:=by
    intro x y hxy
    have hb:=(ordinaryBoundaryGraph_adj R S T W x y).mp hxy
    by_cases hx:x∈Ω
    · by_cases hy:y∈Ω
      · exact Or.inl ((spanningRestriction_adj _ _ _ _).mpr ⟨hb.1,hx,hy⟩)
      · apply Or.inr
        apply (ordinaryBoundaryGraph_adj Q H X Z x y).mpr
        exact ⟨hphys hb.1,Or.inr ⟨hy,hx⟩⟩
    · have hy:y∈Ω:=by
        rcases hb.2 with h|h
        · exact hnested h.2
        · exact (hx (hnested h.2)).elim
      apply Or.inr
      apply (ordinaryBoundaryGraph_adj Q H X Z x y).mpr
      exact ⟨hphys hb.1,Or.inl ⟨hx,hy⟩⟩
  intro w
  have hd:(ordinaryBoundaryGraph R S T W).degree w≤
      (spanningRestriction (ordinaryPhysicalGraph R S) Ω).degree w+
        (ordinaryBoundaryGraph Q H X Z).degree w:=
    (SimpleGraph.degree_le_of_le hsub).trans (graph_degree_sup_le _ _ w)
  have hdR:((ordinaryBoundaryGraph R S T W).degree w:ℝ)≤
      ((spanningRestriction (ordinaryPhysicalGraph R S) Ω).degree w:ℝ)+
        ((ordinaryBoundaryGraph Q H X Z).degree w:ℝ):=by exact_mod_cast hd
  exact hdR.trans (add_le_add (hinner w) (houter w))
end Oberwolfach
