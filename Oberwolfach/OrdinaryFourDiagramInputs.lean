module

public import Oberwolfach.OrdinaryTransformerInput
public import Oberwolfach.OrdinaryActualDiagramDivisibility
public import Oberwolfach.OrdinaryActualCentralBijection

@[expose] public section

/-! The four concrete resource maps between the five embedded graphs.
The comparison identifiers are obtained from divisibility, and all ambient
transformer hypotheses are derived from the actual finite constructions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U:Type} [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]

theorem ordinary_four_diagram_inputs (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop)
    (r m:ℕ) (hr:3≤r) (hm:Fintype.card V₀+Fintype.card U₀≤m)
    (hbal:∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀ u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)
    (Q F:SimpleGraph V) (H:V→U→Prop) (hQF:∀ v w,Q.Adj v w→¬F.Adj v w)
    (A W R₀ R:Finset V) (B₀ B:Finset U)
    (eL:OrdinaryPairHostEmbedding (actualAttachmentRim G Hs (SimpleGraph.cycleGraph r) ⟨0,by omega⟩)
      (actualAttachmentSpokes G Hs (⟨0,by omega⟩:Fin r)) Q H)
    (eR:OrdinaryPairHostEmbedding
      (actualAttachmentRim (ordinaryComparisonRim r (G.edgeFinset.card/r) (by omega))
        (ordinaryComparisonSpokes r (G.edgeFinset.card/r) (by omega)) (SimpleGraph.cycleGraph r) ⟨0,by omega⟩)
      (actualAttachmentSpokes (ordinaryComparisonRim r (G.edgeFinset.card/r) (by omega))
        (ordinaryComparisonSpokes r (G.edgeFinset.card/r) (by omega)) (⟨0,by omega⟩:Fin r)) Q H)
    (e:∀ i:Fin 3,OrdinaryPairHostEmbedding (ordinaryDiagramExpansionRim G Hs r hr i)
      (ordinaryDiagramExpansionSpokes G Hs r hr i) Q H)
    (hfresh:∀ i,(e i).IsFresh F A W ((R₀∪Finset.univ.image eL.row)∪Finset.univ.image eR.row)
      ((B₀∪Finset.univ.image eL.hub)∪Finset.univ.image eR.hub))
    (hdv:∀ i j,i≠j→∀ a b,(e i).row a≠(e j).row b)
    (hdu:∀ i j,i≠j→∀ a b,(e i).hub a≠(e j).hub b)
    (hsep:∀ i j,i≠j→∀ a b,¬F.Adj ((e i).row a) ((e j).row b))
    (hLR:∀ a,eL.row a∈R) (hRR:∀ a,eR.row a∈R) (heR:∀ i a,(e i).row a∈R)
    (hLB:∀ a,eL.hub a∈B) (hRB:∀ a,eR.hub a∈B) (heB:∀ i a,(e i).hub a∈B) :
    ∃ T:Fin 4→OrdinaryTransformerInput r (5*ordinaryDiagramSize r m) Q F H R B,
      (∀ j,ordinaryHostResources (T j).G (T j).K=
        ![(e 0).resources,(e 0).resources,(e 2).resources,(e 2).resources] j)∧
      (∀ j,transformerImageResources (T j).G (T j).K (T j).φ (T j).ψ=
        ![eL.resources,(e 1).resources,(e 1).resources,eR.resources] j) := by
  let z:Fin r:=⟨0,by omega⟩
  let o:Fin r:=⟨r-1,by omega⟩
  let k:=G.edgeFinset.card/r
  let Gc:=ordinaryComparisonRim r k (by omega)
  let Hc:=ordinaryComparisonSpokes r k (by omega)
  have hzo:(SimpleGraph.cycleGraph r).Adj z o:=cycleGraph_zero_last_adj r hr
  have hbalanced:=ordinary_actual_diagram_divisibility G Hs r hr hbal hdiv
  have hsize:=ordinary_diagram_model_size G Hs r m hr hm
  have hrow (i:Fin 3):Fintype.card (ExpansionRow (ordinaryDiagramOldRows G r i)
      (ordinaryDiagramEdges G r hr i) (ordinaryDiagramSpokes G Hs r hr i) (Fin r))≤5*ordinaryDiagramSize r m:=by
    have hh:=hsize i
    simp only [ExpansionRow,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    rw [Nat.mul_add,Nat.mul_one] at hh
    omega
  have hhub (i:Fin 3):Fintype.card (ExpansionHub (ordinaryDiagramOldHubs (U₀:=U₀) G r i)
      (ordinaryDiagramEdges G r hr i) (ordinaryDiagramSpokes G Hs r hr i))≤5*ordinaryDiagramSize r m:=by
    have hh:=hsize i
    simp only [ExpansionHub,Fintype.card_sum]
    rw [Nat.mul_add,Nat.mul_one] at hh
    omega
  have hLdv (i:Fin 3) a b:(e i).row a≠eL.row b:=by
    intro h
    exact (hfresh i).1 a |>.2.2.1 (by rw [h];simp)
  have hRdv (i:Fin 3) a b:(e i).row a≠eR.row b:=by
    intro h
    exact (hfresh i).1 a |>.2.2.1 (by rw [h];simp)
  have hLdu (i:Fin 3) a b:(e i).hub a≠eL.hub b:=by
    intro h
    exact (hfresh i).2.1 a (by rw [h];simp)
  have hRdu (i:Fin 3) a b:(e i).hub a≠eR.hub b:=by
    intro h
    exact (hfresh i).2.1 a (by rw [h];simp)
  have hLsep (i:Fin 3) a b:¬F.Adj ((e i).row a) (eL.row b):=
    (hfresh i).1 a |>.2.2.2 _ (by simp)
  have hRsep (i:Fin 3) a b:¬F.Adj ((e i).row a) (eR.row b):=
    (hfresh i).1 a |>.2.2.2 _ (by simp)
  have hleft:=actual_expansion_attachment_bijection G Hs (SimpleGraph.cycleGraph r) z o hzo
  have hright:=actual_expansion_attachment_bijection Gc Hc (SimpleGraph.cycleGraph r) z o hzo
  obtain ⟨⟨ee⟩,⟨jj⟩⟩:=ordinary_comparison_identifier_equivalences G Hs r hr hbal hdiv
  have hmidL:=actual_finite_expansion_central_bijection G Hs (SimpleGraph.cycleGraph r) z o hzo.ne
    (Equiv.refl _) (Equiv.refl _)
  have hmidR:=actual_finite_expansion_central_bijection Gc Hc (SimpleGraph.cycleGraph r) z o hzo.ne ee jj
  obtain ⟨T0,h0,h0'⟩:=ordinary_embedded_transformer_input _ _ _ _ Q F H (e 0) eL
    (attachmentCollapse z (actualAttachmentRoot G Hs)) id r (5*ordinaryDiagramSize r m) R B
    (hbalanced 0).1 (hbalanced 0).2 (hrow 0) (hhub 0)
    hleft.1 (by ext x;simpa [Finset.mem_image,ordinaryDiagramExpansionRim,ordinaryDiagramExpansionSpokes,ordinaryDiagramOldRows,ordinaryDiagramOldHubs,ordinaryDiagramEdges,ordinaryDiagramSpokes,ordinaryDiagramX,ordinaryDiagramY,ordinaryDiagramV,ordinaryDiagramU,ordinaryDiagramOldRows_fintype,ordinaryDiagramOldHubs_fintype,ordinaryDiagramEdges_fintype,ordinaryDiagramSpokes_fintype,Fin.cases,Fin.induction,Fin.induction.go,actualExpansionRim,actualExpansionSpokes,actualAttachmentRim,actualAttachmentSpokes,actualAttachmentRoot,ordinaryPairResourceMap,attachmentResourceMap,z,o,Gc,Hc,k] using Finset.ext_iff.mp hleft.2 x) (hLdv 0) (hLdu 0) (hLsep 0) hQF (heR 0) hLR (heB 0) hLB
  obtain ⟨T1,h1,h1'⟩:=ordinary_embedded_transformer_input _ _ _ _ Q F H (e 0) (e 1)
    (actualCentralRowMap (W:=Fin r) G Hs (Equiv.refl _) (Equiv.refl _))
    (actualCentralHubMap G Hs (Equiv.refl _) (Equiv.refl _)) r (5*ordinaryDiagramSize r m) R B
    (hbalanced 0).1 (hbalanced 0).2 (hrow 0) (hhub 0)
    hmidL.1 (by ext x;simpa [Finset.mem_image,ordinaryDiagramExpansionRim,ordinaryDiagramExpansionSpokes,ordinaryDiagramOldRows,ordinaryDiagramOldHubs,ordinaryDiagramEdges,ordinaryDiagramSpokes,ordinaryDiagramX,ordinaryDiagramY,ordinaryDiagramV,ordinaryDiagramU,ordinaryDiagramOldRows_fintype,ordinaryDiagramOldHubs_fintype,ordinaryDiagramEdges_fintype,ordinaryDiagramSpokes_fintype,Fin.cases,Fin.induction,Fin.induction.go,actualExpansionRim,actualExpansionSpokes,actualAttachmentRim,actualAttachmentSpokes,actualAttachmentRoot,ordinaryPairResourceMap,attachmentResourceMap,z,o,Gc,Hc,k] using Finset.ext_iff.mp hmidL.2 x) (hdv 0 1 (by decide)) (hdu 0 1 (by decide)) (hsep 0 1 (by decide))
    hQF (heR 0) (heR 1) (heB 0) (heB 1)
  obtain ⟨T2,h2,h2'⟩:=ordinary_embedded_transformer_input _ _ _ _ Q F H (e 2) (e 1)
    (actualCentralRowMap (W:=Fin r) Gc Hc ee jj) (actualCentralHubMap Gc Hc ee jj)
    r (5*ordinaryDiagramSize r m) R B
    (hbalanced 2).1 (hbalanced 2).2 (hrow 2) (hhub 2)
    hmidR.1 (by ext x;simpa [Finset.mem_image,ordinaryDiagramExpansionRim,ordinaryDiagramExpansionSpokes,ordinaryDiagramOldRows,ordinaryDiagramOldHubs,ordinaryDiagramEdges,ordinaryDiagramSpokes,ordinaryDiagramX,ordinaryDiagramY,ordinaryDiagramV,ordinaryDiagramU,ordinaryDiagramOldRows_fintype,ordinaryDiagramOldHubs_fintype,ordinaryDiagramEdges_fintype,ordinaryDiagramSpokes_fintype,Fin.cases,Fin.induction,Fin.induction.go,actualExpansionRim,actualExpansionSpokes,actualAttachmentRim,actualAttachmentSpokes,actualAttachmentRoot,ordinaryPairResourceMap,attachmentResourceMap,z,o,Gc,Hc,k] using Finset.ext_iff.mp hmidR.2 x) (hdv 2 1 (by decide)) (hdu 2 1 (by decide)) (hsep 2 1 (by decide))
    hQF (heR 2) (heR 1) (heB 2) (heB 1)
  obtain ⟨T3,h3,h3'⟩:=ordinary_embedded_transformer_input _ _ _ _ Q F H (e 2) eR
    (attachmentCollapse z (actualAttachmentRoot Gc Hc)) id r (5*ordinaryDiagramSize r m) R B
    (hbalanced 2).1 (hbalanced 2).2 (hrow 2) (hhub 2)
    hright.1 (by ext x;simpa [Finset.mem_image,ordinaryDiagramExpansionRim,ordinaryDiagramExpansionSpokes,ordinaryDiagramOldRows,ordinaryDiagramOldHubs,ordinaryDiagramEdges,ordinaryDiagramSpokes,ordinaryDiagramX,ordinaryDiagramY,ordinaryDiagramV,ordinaryDiagramU,ordinaryDiagramOldRows_fintype,ordinaryDiagramOldHubs_fintype,ordinaryDiagramEdges_fintype,ordinaryDiagramSpokes_fintype,Fin.cases,Fin.induction,Fin.induction.go,actualExpansionRim,actualExpansionSpokes,actualAttachmentRim,actualAttachmentSpokes,actualAttachmentRoot,ordinaryPairResourceMap,attachmentResourceMap,z,o,Gc,Hc,k] using Finset.ext_iff.mp hright.2 x) (hRdv 2) (hRdu 2) (hRsep 2) hQF (heR 2) hRR (heB 2) hRB
  refine ⟨![T0,T1,T2,T3],?_,?_⟩
  · intro i;fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · intro i;fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
    · exact h0'
    · exact h1'
    · exact h2'
    · exact h3'

end Oberwolfach
