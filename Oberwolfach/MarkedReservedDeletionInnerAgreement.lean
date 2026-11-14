module

public import Oberwolfach.MarkedReservedResourceGraphs
public import Oberwolfach.MarkedRawPairUnchangedFromGraphs
public import Oberwolfach.MarkedSampleDeletedArcs

@[expose] public section
/-! Deleting an absorber outside the protected pair leaves the restricted
raw sample and both physical spoke relations unchanged on that pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_deletion_protects_inner_pair
    {W Z:Type} [Fintype W] [Fintype Z] [LinearOrder W] [DecidableEq Z]
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hC:∀ e∈C,¬markedInnerResource I J e)
    (f:W→V) (g:Z→U) (hf:∀ x,f x∈I) (hg:∀ u,g u∈J):
    let DR:=physicalEdgeGraph (markedReservedRimPairs C)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs C);
    rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)=rawMarkedRestrictPair f g σ ∧
    (fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u))=
      (fun b x u=>H b (f x) (g u)):=by
  intro DR DS
  obtain ⟨hr,hs⟩:=marked_reserved_graphs_avoid_internal_resources C I J hC
  exact marked_raw_pair_unchanged_from_graphs σ H DR DS I J hr hs f g hf hg

/-- Every original typed arc whose endpoints lie in the invariant inner
vertex set has the same direction and type after reserving the absorber. -/
theorem marked_reserved_deletion_preserves_inner_arcs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hC:∀ e∈C,¬markedInnerResource I J e):
    let DR:=physicalEdgeGraph (markedReservedRimPairs C)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset;
    ∀ (mark:Bool) (e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) mark),
      e.val.1∈I→e.val.2∈I→
      ∃ e':MarkedSampleArc P π (3*d) (fun a=>σ' (Sum.inl a)) mark,e'.val=e.val :=by
  intro DR σ' mark e h₁ h₂
  have hgraph:∀ x∈I,∀ y∈I,¬DR.Adj x y:=(marked_reserved_graphs_avoid_internal_resources C I J hC).1
  have hy:(if mark then π e.val.2 else e.val.2)∈I:=by
    cases mark <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact h₂
    · exact (hI _).mpr h₂
  have hd:s(e.val.1,if mark then π e.val.2 else e.val.2)∉DR.edgeFinset:=by
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hgraph e.val.1 h₁ _ hy
  have hnew:markedPhysicalRim P π (3*d) (fun a=>σ' (Sum.inl a)) mark e.val.1 e.val.2=1:=
    (markedPhysicalRim_delete_iff P π d σ DR.edgeFinset mark e.val.1 e.val.2).mpr ⟨e.property,hd⟩
  exact ⟨⟨e.val,hnew⟩,rfl⟩
end Oberwolfach
