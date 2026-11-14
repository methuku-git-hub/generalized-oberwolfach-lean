module

public import Oberwolfach.OrdinaryOldEdgesApproximateLayer
public import Oberwolfach.OrdinaryRequiredAvoidsForbidden
public import Oberwolfach.LongApproximateGraphStateInclusion

@[expose] public section
/-! Old pieces embedded in the surviving approximate sample avoid any
required graph disjoint from that sample, including target conflict edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_old_family_avoids_required_edges
    {V U Γ Color : Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    {X A B J : U → Type} [∀ u, Fintype (X u)] [∀ u, DecidableEq (X u)]
    [∀ u, Fintype (A u)] [∀ u, DecidableEq (A u)] [∀ u, DecidableEq (B u)] [∀ u, DecidableEq (J u)]
    (P Host Del G : SimpleGraph V) (hHP : Host ≤ P) (π : Equiv.Perm V) (d : ℕ)
    (σ : ∀ e : RawWheelCoordinate V U, RawExpandedMarkedCoordinateState Γ Color e)
    (F : ∀ u, SimpleGraph (X u)) (data : ∀ u, ActualResidualData (K := A u ⊕ B u) (J := J u) (F u))
    (hempty : ∀ u, IsEmpty (A u)) (hs : ∀ u, (data u).s₁ = firstSumIndices) (ψ : ∀ u, X u → V)
    (hdir : ∀ u, ActualOldImageDirected (data u) (ψ u)
      (rawMixedPhysicalArc Host π d (rawMarkedDeleteRims (fun e => rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset))) :
    let S₀ := longPhysicalStateGraph P σ {0,1,2,3,4};
    (∀ x y, G.Adj x y → ¬(S₀ \ Del).Adj x y) →
    ∀ u, Disjoint ((data u).deletedEdges.image (Sym2.map (ψ u))) G.edgeFinset := by
  intro S₀ hsep u
  have hsub : ({2,3} : Finset (Fin 6)) ⊆ {0,1,2,3,4} := by decide
  have harc : ∀ x y, rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e => rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y →
      (S₀ \ Del).Adj x y := by
    intro x y h
    have he := raw_mixed_deleted_arc_in_approximate_layer P Host Del hHP π d σ x y h
    have ha : (longApproximatePhysicalGraph P π d σ).Adj x y := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    have hp := long_approximate_graph_in_state_graph P π d σ ha
    have hn := (raw_mixed_deleted_arc_host Host Del π d
      (fun e => rawExpandedApproximateCollapse e (σ e)) x y h).2
    exact ⟨⟨hp.1, hsub hp.2⟩, hn⟩
  have hold := actual_old_directed_host_with_empty_final (data u) (hempty u) (hs u) (ψ u)
      (S₀ \ Del) _ harc (hdir u)
  apply Finset.disjoint_left.mpr
  intro e he hg
  have he' := hold he
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hx : (S₀ \ Del).Adj x y := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he'
    have hy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp hg
    exact hsep x y hy hx
end Oberwolfach
