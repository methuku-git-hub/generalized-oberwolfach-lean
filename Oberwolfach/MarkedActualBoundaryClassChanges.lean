module

public import Oberwolfach.MarkedRemainingBoundaryClasses
public import Oberwolfach.PhysicalWheelFamilies
public import Oberwolfach.CommonClassBalanceBounds

@[expose] public section

/-! Fixed-domain class changes for the actual sample after two physical
packings. Both deletions are charged at their realized graph degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Gamma Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Gamma] [Fintype Color]

theorem marked_actual_boundary_class_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ₀:RawMarkedOutcome V U Gamma Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Z:Finset U) (hX:∀ x,π x∈X↔x∈X)
    (CR DR:SimpleGraph V) (CH DH:V→U→Prop) (σ:Sym2 (V⊕U)→Bool) (ℓ δ:ℝ):
    let G:=ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ₀ Finset.univ)
      (fun x u=>H false x u∨H true x u) X Z
    let C:=ordinaryPhysicalGraph CR CH
    let D:=ordinaryPhysicalGraph DR DH;
    Disjoint C (retainedGraph G σ)→
    (∀ x,(((G\retainedGraph G σ)\C).degree x:ℝ)≤ℓ)→
    (∀ x,(D.degree x:ℝ)≤δ)→
    let σ':=rawMarkedDeleteRims σ₀ (CR⊔DR).edgeFinset
    let H':=markedDeletePhysicalSpokes H (C⊔D);
    (∀ mark incoming x,x∉X→
      ((changed (markedEndpointLabels P π d X (mark,incoming,x) σ')
        ((markedEndpointLabels P π d X (mark,incoming,x) σ₀).filter
          (fun v=>σ (markedBoundaryEndpointCoin π mark incoming x (Sum.inl v))=true))).card:ℝ)≤ℓ+δ)∧
    (∀ b x,x∉X→((changed (Z.filter (H' b x))
      ((Z.filter (H b x)).filter (fun u=>σ s(Sum.inl x,Sum.inr u)=true))).card:ℝ)≤ℓ+δ)∧
    (∀ u,u∉Z→((changed
      (X.filter (fun x=>(H false x u∨H true x u)∧¬(C⊔D).Adj (Sum.inl x) (Sum.inr u)))
      ((X.filter (fun x=>H false x u∨H true x u)).filter
        (fun x=>σ s(Sum.inl x,Sum.inr u)=true))).card:ℝ)≤ℓ+δ):=by
  intro G C D hCR hleft hcover σ' H'
  have hb:=marked_sample_boundary_classes_after_packing P π d σ₀ H X Z hX C D σ ℓ δ hCR hleft hcover
  have hrem:G\(C⊔D)=(G\C)\D:=by
    ext x y
    simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj]
    tauto
  have hCD:ordinaryPhysicalGraph (CR⊔DR) (fun x u=>CH x u∨DH x u)=C⊔D:=ordinaryPhysicalGraph_sup _ _ _ _
  refine ⟨?_,?_,?_⟩
  · intro mark incoming x hx
    have he:=marked_remaining_endpoint_class P π d σ₀ H X Z hX (CR⊔DR)
      (fun x u=>CH x u∨DH x u) mark incoming x hx
    dsimp only at he
    rw [hCD] at he
    have he':markedEndpointLabels P π d X (mark,incoming,x) σ'=
      (markedEndpointLabels P π d X (mark,incoming,x) σ₀).filter
      (fun v=>markedBoundaryEndpointCoin π mark incoming x (Sum.inl v)∈(G\(C⊔D)).edgeSet):=by
      convert he using 1 <;> congr!
    simp only [hrem] at he'
    rw [he',changed_symm_eq]
    exact hb.1 mark incoming x hx
  · intro b x hx
    have he:=marked_remaining_spoke_class (markedSampleArcSetGraph P π d σ₀ Finset.univ) H X Z (C⊔D) b x hx
    have he':Z.filter (H' b x)=(Z.filter (H b x)).filter (fun u=>(G\(C⊔D)).Adj (Sum.inl x) (Sum.inr u)):=by
      convert he using 1 <;> congr!
    simp only [hrem] at he'
    rw [he',changed_symm_eq]
    exact hb.2.1 b x hx
  · intro u hu
    have he:=marked_remaining_spoke_column (markedSampleArcSetGraph P π d σ₀ Finset.univ) H X Z (C⊔D) u hu
    have he':X.filter (fun x=>(H false x u∨H true x u)∧¬(C⊔D).Adj (Sum.inl x) (Sum.inr u))=
      (X.filter (fun x=>H false x u∨H true x u)).filter (fun x=>(G\(C⊔D)).Adj (Sum.inl x) (Sum.inr u)):=by
      convert he using 1 <;> congr!
    simp only [hrem] at he'
    rw [he',changed_symm_eq]
    exact hb.2.2 u hu
end Oberwolfach
