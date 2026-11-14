module

public import Oberwolfach.OrdinaryOldEdgesApproximateLayer
public import Oberwolfach.LongApproximateGraphStateInclusion
public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion

@[expose] public section
/-! Old matching edges lie in expanded states 2 and 3, while the selected
reference uses state 0. Hence old pieces consume no selected reference rim. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_old_edges_avoid_selected_reference
    {V U Γ Color X A B J : Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] [Fintype X] [DecidableEq X]
    [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    (P Host Del : SimpleGraph V) (hHost : Host ≤ P) (π : Equiv.Perm V) (d : ℕ)
    (σ : ∀ e : RawWheelCoordinate V U, RawExpandedMarkedCoordinateState Γ Color e)
    {F : SimpleGraph X} (data : ActualResidualData (K := A ⊕ B) (J := J) F)
    (hempty : IsEmpty A) (hs : data.s₁ = firstSumIndices) (ψ : X → V)
    (hdir : ActualOldImageDirected data ψ (rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e => rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset))) :
    Disjoint (data.deletedEdges.image (Sym2.map ψ))
      (rawWheelGraph P (fun e => expandedOrdinarySelectedCollapse e (σ e))).edgeFinset := by
  have hold := ordinary_old_edges_in_approximate_layer P Host Del hHost π d σ data hempty hs ψ hdir
  apply Finset.disjoint_left.mpr
  intro e he hr
  have he' := hold he
  induction e using Sym2.inductionOn with
  | _ v w =>
    have ha : (longApproximatePhysicalGraph P π d σ).Adj v w := by
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he'
    have h23 := long_approximate_graph_in_state_graph P π d σ ha
    have h0 : (longPhysicalStateGraph P σ {0}).Adj v w := by
      rw [←ordinary_shared_sample_reference_graph_eq_state_zero]
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hr
    change P.Adj v w ∧ (σ (Sum.inl s(v,w))).1 ∈ ({2,3}:Finset (Fin 6)) at h23
    change P.Adj v w ∧ (σ (Sum.inl s(v,w))).1 ∈ ({0}:Finset (Fin 6)) at h0
    have hne : (2 : Fin 6) ≠ 0 ∧ (3 : Fin 6) ≠ 0 := by decide
    simp only [Finset.mem_insert,Finset.mem_singleton] at h23
    simp only [Finset.mem_singleton] at h0
    rcases h23.2 with h2 | h3
    · exact hne.1 (h2.symm.trans h0.2)
    · exact hne.2 (h3.symm.trans h0.2)
end Oberwolfach
