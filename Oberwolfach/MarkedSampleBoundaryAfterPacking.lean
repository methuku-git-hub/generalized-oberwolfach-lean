module

public import Oberwolfach.MarkedSampleBoundaryPhysicalGraph
public import Oberwolfach.MarkedBoundaryMaskAfterPacking
public import Oberwolfach.PhysicalBoundaryClassesAfterPacking

@[expose] public section

/-! The actual marked boundary remainder after the approximate packing
and subsequent covering has the required fixed-domain class changes.
All roots remain in the ambient domains and the bound has no extra factor
of the reservation probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Gamma Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Gamma] [Fintype Color]

theorem marked_sample_boundary_classes_after_packing (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ₀:RawMarkedOutcome V U Gamma Color) (H:Bool→V→U→Prop)
    (X:Finset V) (Z:Finset U) (hX:∀ v,π v∈X↔v∈X)
    (C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (ℓ δ:ℝ)
    (hCR:Disjoint C (retainedGraph (ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ₀ Finset.univ)
      (fun v u=>H false v u∨H true v u) X Z) σ))
    (hleft:∀ z,((((ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ₀ Finset.univ)
      (fun v u=>H false v u∨H true v u) X Z)\retainedGraph
      (ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ₀ Finset.univ)
      (fun v u=>H false v u∨H true v u) X Z) σ)\C).degree z:ℝ)≤ℓ)
    (hcover:∀ z,(D.degree z:ℝ)≤δ):
    let G:=ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ₀ Finset.univ)
      (fun v u=>H false v u∨H true v u) X Z
    let R:=(G\C)\D;
    (∀ mark incoming x,x∉X→
      ((changed ((markedEndpointLabels P π d X (mark,incoming,x) σ₀).filter
        (fun v=>σ (markedBoundaryEndpointCoin π mark incoming x (Sum.inl v))=true))
        ((markedEndpointLabels P π d X (mark,incoming,x) σ₀).filter
        (fun v=>markedBoundaryEndpointCoin π mark incoming x (Sum.inl v)∈R.edgeSet))).card:ℝ)≤ℓ+δ) ∧
    (∀ b x,x∉X→
      ((changed ((Z.filter (H b x)).filter (fun u=>σ s(Sum.inl x,Sum.inr u)=true))
        ((Z.filter (H b x)).filter (fun u=>R.Adj (Sum.inl x) (Sum.inr u)))).card:ℝ)≤ℓ+δ) ∧
    (∀ u,u∉Z→
      ((changed ((X.filter (fun x=>H false x u∨H true x u)).filter
        (fun x=>σ s(Sum.inl x,Sum.inr u)=true))
        ((X.filter (fun x=>H false x u∨H true x u)).filter
        (fun x=>R.Adj (Sum.inl x) (Sum.inr u)))).card:ℝ)≤ℓ+δ):=by
  intro G R
  have hbound {T:Type} [DecidableEq T] (S:Finset T) (x:V⊕U)
      (h:S.card≤((G\retainedGraph G σ)\C).degree x+D.degree x):(S.card:ℝ)≤ℓ+δ:=by
    have hh:(S.card:ℝ)≤((G\retainedGraph G σ)\C).degree x+D.degree x:=by exact_mod_cast h
    exact hh.trans (add_le_add (hleft x) (hcover x))
  refine ⟨?_,?_,?_⟩
  · intro mark incoming x hx
    apply hbound _ (Sum.inl (if mark&&incoming then π x else x))
    apply marked_endpoint_class_after_packing π mark incoming x _ G C D σ _ hCR
    intro v hv
    exact marked_sample_endpoint_coin_mem_boundary P π d σ₀ H X Z hX mark incoming x hx v hv
  · intro b x hx
    apply hbound _ (Sum.inl x)
    apply marked_spoke_class_after_packing x _ G C D σ _ hCR
    intro u hu
    obtain ⟨hu,hH⟩:=Finset.mem_filter.mp hu
    change G.Adj (Sum.inl x) (Sum.inr u)
    rw [ordinaryBoundaryGraph_adj]
    refine ⟨?_,?_⟩
    · cases b <;> simp only [ordinaryPhysicalGraph] <;> tauto
    · simp [ordinaryInnerVertices_left,ordinaryInnerVertices_right,hx,hu]
  · intro u hu
    apply hbound _ (Sum.inr u)
    apply marked_spoke_column_after_packing u _ G C D σ _ hCR
    intro x hx
    obtain ⟨hx,hH⟩:=Finset.mem_filter.mp hx
    change G.Adj (Sum.inl x) (Sum.inr u)
    rw [ordinaryBoundaryGraph_adj]
    refine ⟨hH,?_⟩
    simp [ordinaryInnerVertices_left,ordinaryInnerVertices_right,hx,hu]

end Oberwolfach
