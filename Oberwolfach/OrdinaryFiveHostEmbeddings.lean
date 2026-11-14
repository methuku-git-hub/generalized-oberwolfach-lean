module

public import Oberwolfach.OrdinaryActualDiagramModels

@[expose] public section

/-! Construct all five finite graph pairs of the ordinary terminal-absorber
diagram together in the actual host. The original pair is preserved in the
first attachment; the final attachment has an actual wheel decomposition.
Every expansion is separated from both attachments and from the others. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1536
set_option maxHeartbeats 28000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U:Type} [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]

theorem ordinary_five_host_embeddings (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop)
    (r m:ℕ) (hr:3≤r) (hm:Fintype.card V₀+Fintype.card U₀≤m)
    (Q F:SimpleGraph V) (H:V→U→Prop) (A W R:Finset V) (B:Finset U)
    (φ:V₀↪V) (ψ:U₀↪U) (hφ:∀ v,φ v∈R) (hψ:∀ u,ψ u∈B)
    (hG:∀ v w,G.Adj v w→Q.Adj (φ v) (φ w)) (hHs:∀ v u,Hs v u→H (φ v) (ψ u))
    (d c cH:ℝ) (hd:0≤d) (hF:∀ v,(F.degree v:ℝ)≤d)
    (hA:c≤(A.card:ℝ)) (hU:cH≤(Fintype.card U:ℝ))
    (hcount:∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hpair:∀ a b v w,c≤(((A.filter (fun z=>H z a∧H z b))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hhub:∀ T:Finset V,T.card≤r→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      cH≤((common Finset.univ T (fun v=>Finset.univ.filter (H v))).card:ℝ))
    (hbudget:W.card+((R.card:ℝ)+6*ordinaryDiagramSize r m+r+6)*(d+1)<c)
    (hB:(B.card:ℝ)+6*ordinaryDiagramSize r m<cH) :
    let k:=G.edgeFinset.card/r
    let Gc:=ordinaryComparisonRim r k (by omega)
    let Hc:=ordinaryComparisonSpokes r k (by omega)
    ∃ eL:OrdinaryPairHostEmbedding (actualAttachmentRim G Hs (SimpleGraph.cycleGraph r) ⟨0,by omega⟩)
        (actualAttachmentSpokes G Hs (⟨0,by omega⟩:Fin r)) Q H,
      (∀ a,eL.row (.inl a)=φ a)∧(∀ a,eL.hub (.inl a)=ψ a)∧
      (∀ i w,eL.row (.inr (i,w))∈A∧eL.row (.inr (i,w))∉W∧eL.row (.inr (i,w))∉R∧
        ∀ z∈R,¬F.Adj (eL.row (.inr (i,w))) z)∧
      (∀ i,eL.hub (.inr i)∉B)∧
      ∃ extra:Finset (Sym2 V⊕(V×U)),
        eL.resources=ordinaryHostResources (G.map φ) (ordinaryMappedSpokes Hs φ ψ)∪extra∧
        Disjoint (ordinaryHostResources (G.map φ) (ordinaryMappedSpokes Hs φ ψ)) extra∧
        HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) extra∧
        ∃ eR:OrdinaryPairHostEmbedding (actualAttachmentRim Gc Hc (SimpleGraph.cycleGraph r) ⟨0,by omega⟩)
            (actualAttachmentSpokes Gc Hc (⟨0,by omega⟩:Fin r)) Q H,
          eR.IsFresh F A W (R∪Finset.univ.image eL.row) (B∪Finset.univ.image eL.hub)∧
          HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) eR.resources∧
          ∃ e:∀ i:Fin 3,OrdinaryPairHostEmbedding (ordinaryDiagramExpansionRim G Hs r hr i)
              (ordinaryDiagramExpansionSpokes G Hs r hr i) Q H,
            (∀ i,(e i).IsFresh F A W ((R∪Finset.univ.image eL.row)∪Finset.univ.image eR.row)
              ((B∪Finset.univ.image eL.hub)∪Finset.univ.image eR.hub))∧
            (∀ i j,i≠j→∀ a b,(e i).row a≠(e j).row b)∧
            (∀ i j,i≠j→∀ a b,(e i).hub a≠(e j).hub b)∧
            (∀ i j,i≠j→∀ a b,¬F.Adj ((e i).row a) ((e j).row b)) := by
  dsimp only
  let k:=G.edgeFinset.card/r
  let Gc:=ordinaryComparisonRim r k (by omega)
  let Hc:=ordinaryComparisonSpokes r k (by omega)
  let M:=ordinaryDiagramSize r m
  have hd1:0≤d+1:=by linarith
  have hM:0≤(M:ℝ):=by positivity
  have hLsize:Fintype.card (ActualExpansionRow G Hs (Fin r))+Fintype.card (ActualExpansionHub G Hs)≤M:=
    (actual_expansion_order_bound G Hs r m hm).trans (by dsimp [M,ordinaryDiagramSize];omega)
  have hJord:=ordinary_comparison_order_bound G r m (by omega)
  have hRsize:Fintype.card (ActualExpansionRow Gc Hc (Fin r))+Fintype.card (ActualExpansionHub Gc Hc)≤M:=
    (actual_expansion_order_bound Gc Hc r (m^2*(r+2)) hJord).trans (by dsimp [M,ordinaryDiagramSize];omega)
  have hLv:Fintype.card (V₀⊕((G.edgeFinset⊕ActualSpoke Hs)×Fin r))≤M:=by
    simpa only [ActualExpansionRow,ExpansionRow] using (Nat.le_add_right _ _).trans hLsize
  have hLhub:Fintype.card (U₀⊕(G.edgeFinset⊕ActualSpoke Hs))≤M:=by
    simpa only [ActualExpansionHub,ExpansionHub] using (Nat.le_add_left _ _).trans hLsize
  have hRv:Fintype.card (OrdinaryComparisonRows r k⊕((Gc.edgeFinset⊕ActualSpoke Hc)×Fin r))≤M:=by
    simpa only [ActualExpansionRow,ExpansionRow] using (Nat.le_add_right _ _).trans hRsize
  have hRhub:Fintype.card (OrdinaryComparisonHubs k⊕(Gc.edgeFinset⊕ActualSpoke Hc))≤M:=by
    simpa only [ActualExpansionHub,ExpansionHub] using (Nat.le_add_left _ _).trans hRsize
  have hLi:(Fintype.card (G.edgeFinset⊕ActualSpoke Hs):ℝ)*r≤M:=by
    have hh:=hLsize
    simp only [ActualExpansionRow,ActualExpansionHub,ExpansionRow,ExpansionHub,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at hh
    exact_mod_cast (show Fintype.card (G.edgeFinset⊕ActualSpoke Hs)*r≤M by simpa only [Fintype.card_sum] using (show (Fintype.card G.edgeFinset+Fintype.card (ActualSpoke Hs))*r≤M by omega))
  have hLh:(Fintype.card (G.edgeFinset⊕ActualSpoke Hs):ℝ)≤M:=by
    have hh:=hLsize
    simp only [ActualExpansionRow,ActualExpansionHub,ExpansionRow,ExpansionHub,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at hh
    exact_mod_cast (show Fintype.card (G.edgeFinset⊕ActualSpoke Hs)≤M by simpa only [Fintype.card_sum] using (show Fintype.card G.edgeFinset+Fintype.card (ActualSpoke Hs)≤M by omega))
  obtain ⟨fL,gL,hfL,hgL,hpriv,hnewhub,hprivF,hQL,hHL,hpartition,hdis,hextra⟩:=
    ordinary_relative_attachment_realization Q F H A W R B φ ψ G Hs (actualAttachmentRoot G Hs)
      hφ hψ hG hHs r hr d c cH hd hF hcount hhub
      (by have hh:=mul_le_mul_of_nonneg_right (show (R.card:ℝ)+Fintype.card (G.edgeFinset⊕ActualSpoke Hs)*r+r+6≤R.card+6*M+r+6 by linarith only [hLi,hM]) hd1
          linarith only [hbudget,hh])
      (by linarith only [hB,hLh,hM])
  let eL:OrdinaryPairHostEmbedding (actualAttachmentRim G Hs (SimpleGraph.cycleGraph r) ⟨0,by omega⟩)
      (actualAttachmentSpokes G Hs (⟨0,by omega⟩:Fin r)) Q H:=⟨fL,gL,hQL,hHL⟩
  refine ⟨eL,hfL,hgL,hpriv,hnewhub,_,hpartition,hdis,hextra,?_⟩
  let RL:=R∪Finset.univ.image fL
  let BL:=B∪Finset.univ.image gL
  have hRL:(RL.card:ℝ)≤R.card+M:=by
    have hc:(Finset.univ.image fL).card≤M:=Finset.card_image_le.trans ((Finset.card_univ).trans_le hLv)
    exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left hc _)
  have hBL:(BL.card:ℝ)≤B.card+M:=by
    have hc:(Finset.univ.image gL).card≤M:=Finset.card_image_le.trans ((Finset.card_univ).trans_le hLhub)
    exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left hc _)
  have hRi:(k:ℝ)+k*r+Fintype.card (Gc.edgeFinset⊕ActualSpoke Hc)*r≤M:=by
    have hh:=hRv
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,OrdinaryComparisonRows] at hh
    have hs:k+k*r+Fintype.card (Gc.edgeFinset⊕ActualSpoke Hc)*r≤M:=by
      simpa only [Fintype.card_sum] using hh
    exact_mod_cast hs
  have hRh:(k:ℝ)+Fintype.card (Gc.edgeFinset⊕ActualSpoke Hc)≤M:=by
    have hh:=hRhub
    simp only [Fintype.card_sum,OrdinaryComparisonHubs,Fintype.card_empty,Fintype.card_fin,zero_add] at hh
    have hs:k+Fintype.card (Gc.edgeFinset⊕ActualSpoke Hc)≤M:=by
      simpa only [Fintype.card_sum] using hh
    exact_mod_cast hs
  obtain ⟨fR,gR,hfR,hgR,hFR,hQR,hHR,hdecR⟩:=ordinary_fresh_comparison_attachment Q F H A W RL BL r k hr
    (actualAttachmentRoot Gc Hc) d c cH hd hF hA hcount hhub
    (by have hh:=mul_le_mul_of_nonneg_right (show (RL.card:ℝ)+k+k*r+Fintype.card (Gc.edgeFinset⊕ActualSpoke Hc)*r+r+6≤R.card+6*M+r+6 by linarith only [hRL,hRi,hM]) hd1
        linarith only [hbudget,hh])
    (by linarith only [hB,hBL,hRh,hM])
  let eR:OrdinaryPairHostEmbedding (actualAttachmentRim Gc Hc (SimpleGraph.cycleGraph r) ⟨0,by omega⟩)
      (actualAttachmentSpokes Gc Hc (⟨0,by omega⟩:Fin r)) Q H:=⟨fR,gR,hQR,hHR⟩
  refine ⟨eR,⟨hfR,hgR,hFR⟩,hdecR,?_⟩
  let R':=RL∪Finset.univ.image fR
  let B':=BL∪Finset.univ.image gR
  have hRR:(R'.card:ℝ)≤R.card+2*M:=by
    have hc:(Finset.univ.image fR).card≤M:=Finset.card_image_le.trans ((Finset.card_univ).trans_le hRv)
    have hh:(R'.card:ℝ)≤RL.card+M:=by exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left hc _)
    linarith only [hRL,hh]
  have hBB:(B'.card:ℝ)≤B.card+2*M:=by
    have hc:(Finset.univ.image gR).card≤M:=Finset.card_image_le.trans ((Finset.card_univ).trans_le hRhub)
    have hh:(B'.card:ℝ)≤BL.card+M:=by exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left hc _)
    linarith only [hBL,hh]
  exact ordinary_joint_expansion_embeddings 3 M r hr
    (ordinaryDiagramOldRows G r) (ordinaryDiagramOldHubs (U₀:=U₀) G r)
    (ordinaryDiagramEdges G r hr) (ordinaryDiagramSpokes G Hs r hr)
    (ordinaryDiagramX G r hr) (ordinaryDiagramY G r hr) (ordinaryDiagramV G Hs r hr) (ordinaryDiagramU G Hs r hr)
    (ordinary_diagram_model_size G Hs r m hr hm) Q F H A W R' B' d c cH hd hF hA hU hcount hpair hhub
    (by norm_num
        have hh:=mul_le_mul_of_nonneg_right hRR hd1
        nlinarith only [hbudget,hh])
    (by norm_num;linarith only [hB,hBB])

end Oberwolfach
