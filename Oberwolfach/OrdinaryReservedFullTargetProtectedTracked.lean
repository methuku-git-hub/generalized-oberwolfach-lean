module

public import Oberwolfach.OrdinaryForcedPlacementAbsorberAvoidance
public import Oberwolfach.OrdinaryReservedForcedTargets
public import Oberwolfach.OrdinarySelectedForcedTargetGlue

@[expose] public section
/-! Required-edge assignment, reserved-list placement and old matching
embeddings combine into whole unreserved factors in the edited target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_full_target_embedding_protected_tracked
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hnpos:0<n)
    {X A B J:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    [∀u,Fintype (A u)] [∀u,DecidableEq (A u)] [∀u,DecidableEq (B u)] [∀u,DecidableEq (J u)]
    (P Host Del Target G:SimpleGraph (Fin n)) (hHost:Host≤P) (hG:G≤Target)
    (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hDel:longPhysicalStateGraph P σ {0,1,2,3,4}\Target≤Del)
    (hsep:∀x y,G.Adj x y→¬(longPhysicalStateGraph P σ {0,1,2,3,4}\Del).Adj x y)
    (Inner:Finset U) (Abs L:U→Finset (Fin n))
    (hLsub:∀u,L u⊆rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u)
    (hAbsSub:∀u,Abs u⊆rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u)
    (hLAvoid:∀u,Disjoint (L u) (Abs u))
    (ρ₀ smin b:ℝ) (hρ:0<ρ₀) (hsmin:0<smin) (hb:0≤b)
    (hUlo:ρ₀*n≤4*(Fintype.card U:ℝ))
    (hinner:(Inner.card:ℝ)≤(5*ρ₀*smin^2/128)*n)
    (herror:(n:ℝ)^(3/4:ℝ)≤(5*ρ₀*smin^2/128)*n)
    (hpair:∀x y,x≠y→(5/8:ℝ)*smin^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ))
    (hbsmall:b≤(5*ρ₀*smin^2/128)/16)
    (hAbs:∀v,((Finset.univ.filter (fun u=>v∈Abs u)).card:ℝ)≤b*n)
    (hdegree:∀v,(G.degree v:ℝ)≤b*n)
    (hempty:∀u,IsEmpty (A u)) (len:∀u,A u→ℕ) (inner:∀u (i:A u),Fin (len u i+1)↪X u)
    (F:∀u,SimpleGraph (X u)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (data:∀u,ActualResidualData (K:=A u⊕B u) (J:=J u) (F u))
    (hs:∀u,(data u).s₁=firstSumIndices)
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (Old:∀u,Finset (X u)) (hPresOld:∀u,(data u).prescribed⊆Old u)
    (hOldEq:∀u,Old u=(data u).oldDomain\bufferedPathStrictInterior (len u) (inner u))
    (ψ:∀u,X u→Fin n) (hψ:∀u,Set.InjOn (ψ u) (↑(Old u):Set (X u)))
    (hOldRaw:∀u,Disjoint (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) ((Old u).image (ψ u)))
    (hdir:∀u,ActualOldImageDirected (data u) (ψ u)
      (rawMixedPhysicalArc Host π d (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset)))
    (hOO:∀u v,u≠v→Disjoint ((data u).deletedEdges.image (Sym2.map (ψ u))) ((data v).deletedEdges.image (Sym2.map (ψ v))))
    (T:U→Finset (Fin n)) (hTAvoid:∀u,Disjoint (T u) (Abs u))
    (InnerV:Finset (Fin n)) (hLInner:∀u,Disjoint (L u) InnerV)
    (hTReserve:∀u,u∈Inner→Disjoint (T u) (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u))
    (hcapacity:∀u,8*(residualSubtypeSet (data u).remaining (data u).prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/((5*ρ₀*smin^2/128)*n)⌉₊+4*((T u\(Old u).image (ψ u)).card)+10≤Fintype.card {x // x∈(data u).remaining})
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2) (hbδ:b≤δ)
    (hnβ:100/β≤(n:ℝ)) (hn:2/Real.sqrt δ≤(n:ℝ)) (hU:Fintype.card U≤n)
    (hsize:∀u,(Fintype.card {x // x∈(data u).remaining}:ℝ)≤δ*n)
    (hload:∀v,((Finset.univ.filter (fun u=>v∈
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1))).card:ℝ)+G.degree v+
      ((Finset.univ.filter (fun u=>v∈T u\(Old u).image (ψ u))).card:ℝ)≤δ*n)
    (hext:∀u,IsExtendingList
      (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y) (L u) β):
    ∃(M:U→Finset (Fin n×Fin n)) (f:∀u,X u↪Fin n),
      (∀u,u∈Inner→M u=∅) ∧
      (∀u,prescribedMatchingEndpoints (M u)⊆rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u\Abs u) ∧
      (∀u,(M u).image prescribedArcPhysical⊆G.edgeFinset) ∧
      (∀u v,v∈T u→∃x,f u x=v) ∧
      (∀u x,x∈(data u).oldDomain→f u x=ψ u x) ∧
      (∀u x,f u x∉Abs u) ∧
      (∀u x y,(F u).Adj x y→Target.Adj (f u x) (f u y)) ∧
      (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly (X u) (F u) (f u))
        (partialFactorPhysicalEdgesPoly (X v) (F v) (f v))) ∧
      (∀u,u∈Inner→∀x,f u x∈InnerV→f u x∉rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u) ∧
      ∃New:U→Finset (Sym2 (Fin n)),
        (∀u,((F u).edgeFinset).image (Sym2.map (f u))=(data u).deletedEdges.image (Sym2.map (ψ u))∪New u) ∧
        PairwisePhysicalDisjoint New ∧
        (∀e∈G.edgeFinset,∃u,e∈New u) ∧
        (∀v,((prescribedPhysicalUnion New).degree v:ℝ)≤5*Real.sqrt δ*n) :=by
  let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
  let Dstar:=fun x y=>Dfree x y ∨ G.Adj x y
  obtain ⟨hOldTarget,hDstar,hDD,hstar,hselected⟩:=ordinary_selected_required_directed_target P Target Host Del G hHost hG π d σ hDel
  have hJ:∀v,(G.degree v:ℝ)≤δ*n:=by
    intro v
    exact (hdegree v).trans (mul_le_mul_of_nonneg_right hbδ (by positivity))
  obtain ⟨D,pieces,M,Bset,g,Φ,hgraph,harcs,hM,hOldM,hMlist,hMinner,hMsub,hinj,hB,hT,hΦ,hΦL,hΦarc,hEpair,hME,hcover,havoid,hdeg⟩:=
    ordinary_reserved_assignment_and_forced_targets hnpos π d (fun e=>σ (Sum.inr e)) G G Dstar Dfree hDstar hDD Inner Abs L hLsub
      ρ₀ smin b hρ hsmin hb hUlo hinner herror hpair hbsmall hAbs hdegree F hF data hCycle Old hPresOld ψ hψ hOldRaw T hcapacity
      β δ hβ hβ1 hδ hδbound hnβ hn hU hsize hload hJ hext
  have hL:∀u,Disjoint (L u) ((Old u).image (ψ u)):=fun u=>(hOldRaw u).mono_left (hLsub u)
  obtain ⟨f,hfold,hfnew,hfcover,hhost,hdis⟩:=ordinary_selected_forced_target_glue hnpos P Host Del Target G hHost hG π d σ hDel hsep
    hempty len inner F hF data hs hCycle Old hOldEq ψ hψ hdir hOO L T hL pieces hgraph M Bset g Φ hinj hB hOldM hT hΦ hΦL hΦarc hMsub hEpair
  have hInt:∀u,bufferedPathStrictInterior (len u) (inner u)=∅:=by
    intro u
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i,_,_⟩:=Finset.mem_biUnion.mp hx
    exact (hempty u).false i
  have hOldFull:∀u,Old u=(data u).oldDomain:=by
    intro u
    simpa only [hInt u,Finset.sdiff_empty] using hOldEq u
  have hOldAbs:∀u,Disjoint ((data u).oldDomain.image (ψ u)) (Abs u):=by
    intro u
    have hh:Disjoint ((Old u).image (ψ u)) (Abs u):=(hOldRaw u).symm.mono_right (hAbsSub u)
    simpa only [hOldFull u] using hh
  have hEndsAbs:∀u,Disjoint (prescribedMatchingEndpoints (M u)) (Abs u):=by
    intro u
    apply Finset.disjoint_left.mpr
    intro v hv ha
    exact (Finset.mem_sdiff.mp (hMlist u hv)).2 ha
  have hAvoid:∀u x,f u x∉Abs u:=by
    intro u
    exact ordinary_forced_placement_avoids_absorber (F u) (data u) (hCycle u) (ψ u) (f u) (Φ u) (g u)
      (Bset u) (prescribedMatchingEndpoints (M u)) (T u) (L u) (Abs u) (Old u)
      (hfold u) (hfnew u) (hΦ u) (hΦL u) ((hB u).2.2.1) (hEndsAbs u) (hTAvoid u) (hLAvoid u) (hOldAbs u)
  have hLocal:∀u,u∈Inner→∀x,f u x∈InnerV→f u x∉rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u:=by
    intro u hu
    let Bad:=InnerV∩rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u
    have hEnds:Disjoint (prescribedMatchingEndpoints (M u)) Bad:=by
      rw [hMinner u hu]
      simp [prescribedMatchingEndpoints]
    have hTarget:Disjoint (T u) Bad:=(hTReserve u hu).mono_right Finset.inter_subset_right
    have hFree:Disjoint (L u) Bad:=(hLInner u).mono_right Finset.inter_subset_left
    have hOldBad:Disjoint ((data u).oldDomain.image (ψ u)) Bad:=by
      have hh:Disjoint ((Old u).image (ψ u)) (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u):=(hOldRaw u).symm
      rw [hOldFull u] at hh
      exact hh.mono_right Finset.inter_subset_right
    have hh:=ordinary_forced_placement_avoids_absorber (F u) (data u) (hCycle u) (ψ u) (f u) (Φ u) (g u)
      (Bset u) (prescribedMatchingEndpoints (M u)) (T u) (L u) Bad (Old u)
      (hfold u) (hfnew u) (hΦ u) (hΦL u) ((hB u).2.2.1) hEnds hTarget hFree hOldBad
    intro x hx hr
    exact hh x (Finset.mem_inter.mpr ⟨hx,hr⟩)
  let New:U→Finset (Sym2 (Fin n)):=fun u=>((prescribedDependentGraph pieces u).edgeFinset).image (Sym2.map (Φ u))
  have hpart:∀u,((F u).edgeFinset).image (Sym2.map (f u))=(data u).deletedEdges.image (Sym2.map (ψ u))∪New u:=by
    intro u
    have hh:=(data u).glued_factor_edge_images (hF u) (hCycle u) (ψ u) (f u) (Φ u) (hfold u) (hfnew u)
    have hgraphEdges:(prescribedDependentGraph pieces u).edgeFinset=
        ((data u).graph.induce (fun x=>x∈(data u).remaining)).edgeFinset:=by
      ext e
      simp only [SimpleGraph.mem_edgeFinset]
      rw [hgraph u]
      rfl
    dsimp [New]
    rw [hgraphEdges]
    convert hh using 1 <;> congr 2 <;> apply graph_edge_finset_instance_eq
  exact ⟨M,f,hMinner,hMlist,hMsub,hfcover,hfold,hAvoid,hhost,hdis,hLocal,New,hpart,hEpair,hcover,hdeg⟩
end Oberwolfach
