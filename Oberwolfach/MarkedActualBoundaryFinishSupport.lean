module

public import Oberwolfach.MarkedMixedBoundaryFinishAfterPackingsSupport
public import Oberwolfach.MarkedPackingRemainingEndpoints
public import Oberwolfach.MarkedPackingRemainingSpokes
public import Oberwolfach.MarkedPackingPhysicalUnion

@[expose] public section

/-! The selected boundary is completed using the actual surviving arcs
and spokes after the two preceding packings. Their incidence embeddings,
exhaustion and all resource exclusions are proved here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_actual_boundary_finish_support (l:ℕ) (hl:1≤l) (β ν:ℝ) (hβ:0<β) (hν:0<ν):
    ∃ pmax:ℝ,0<pmax∧pmax≤1∧∀ p:ℝ,0<p→p≤pmax→∀ d:ℕ,1≤d→∃ n₀:ℕ,
    ∀ (V U Gamma Color J I:Type) [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
      [Fintype Gamma] [Fintype Color] [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I],
      n₀≤Fintype.card (V⊕U)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (σ:RawMarkedOutcome V U Gamma Color)
      (H:Bool→V→U→Prop) (X:Finset V) (Z:Finset U),
      (∀ x,π x∈X↔x∈X)→(∀ x u,¬(H false x u∧H true x u))→
      (∀ u v z,H false v u→H true z u→v≠π z)→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let T:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:T=>e.val.1
    let khead:=fun e:T=>e.val.2;
    ∀ Qext:MarkedBoundaryExtensionCounts tail head ktail khead (H false) (H true) X (β*Fintype.card (V⊕U)),
    ∀ (root:J↪V) (hub:I↪U),(∀ j,root j∉X)→(∀ i,hub i∉Z)→
      (∀ v∉X,∃ j,root j=v)→(∀ u∉Z,∃ i,hub i=u)→
    ∀ M₀ M₁:Finset (MarkedWheel tail head ktail khead (l+4) π (3*d) (H false) (H true)),
      (∀ W∈M₀,∀ W'∈M₀,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
      (∀ W∈M₁,∀ W'∈M₁,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
      Disjoint (M₀.biUnion markedWheelPhysicalResources) (M₁.biUnion markedWheelPhysicalResources)→
      (∀ e∈M₀.biUnion markedWheelPhysicalResources,¬markedInnerResource X Z e)→
      (∀ a:E⊕T,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
        Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈(M₀∪M₁).biUnion markedWheelPhysicalResources)→
      (∀ x u,x∉X→u∉Z→H false x u∨H true x u→Sum.inr (x,u)∈(M₀∪M₁).biUnion markedWheelPhysicalResources)→
    let C:=ordinaryPhysicalGraph (markedPackingRimGraph (M₀∪M₁)) (markedPackingSpokes (M₀∪M₁))
    let D₁:=ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)
    let σ':=rawMarkedDeleteRims σ (markedPackingRimGraph (M₀∪M₁)).edgeFinset
    let H':=markedDeletePhysicalSpokes H C
    let A₀:=fun j:J=>markedEndpointLabels P π d X (false,true,root j) σ'
    let A₁:=fun j:J=>markedEndpointLabels P π d X (true,true,root j) σ'
    let X₀:=fun j:J=>markedEndpointLabels P π d X (false,false,root j) σ'
    let X₁:=fun j:J=>markedEndpointLabels P π d X (true,false,root j) σ'
    let Y₀:=fun j:J=>Z.filter (H' false (root j))
    let Y₁:=fun j:J=>Z.filter (H' true (root j))
    let Y:=fun i:I=>X.filter (fun x=>(H false x (hub i)∨H true x (hub i))∧¬C.Adj (Sum.inl x) (Sum.inr (hub i)));
      (∀ z,(D₁.degree z:ℝ)≤p^3*Fintype.card (V⊕U))→
    ∀ (F:∀ i,MarkedHubFactorOn tail head ktail khead (l+4) π (3*d) (H false) (H true) (hub i) (Y i))
      (Q:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) (H false) (H true) π (3*d)),
    let K:I⊕J→SimpleGraph (V⊕U):=Sum.elim (fun i=>(F i).graph) (fun j=>(Q j).graph);
      (∀ i j,i≠j→Disjoint (K i) (K j))→(∀ i,Disjoint (K i) D₁)→
      (∀ z,((⨆ i,K i).degree z:ℝ)≤56*p*Fintype.card (V⊕U))→
    ∃ N:Finset (MarkedWheel tail head ktail khead (l+4) π (3*d) (H false) (H true)),
      Disjoint ((M₀∪M₁).biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources)∧
      (let M:=M₀∪M₁∪N
       (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
       (∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ v∈X,((Z.filter (markedPackingSpokes M v)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ u∈Z,((X.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (let A':=Finset.univ\M.biUnion markedWheelArcs
        let S':=(Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2))\M.biUnion markedWheelSpokePairs
        (∀ a∈A',Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)∧
          (∀ s∈S',s.1∈X∧s.2∈Z)∧
          (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
            (Finset.univ.image (fun a:E⊕T=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
              (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)).image Sum.inr)\
              M.biUnion markedWheelPhysicalResources)):=by
  obtain ⟨p₀,hp₀,hp₀1,hfinish⟩:=marked_mixed_boundary_finish_after_packings_support (l+1) (by omega) β ν hβ hν
  refine ⟨min p₀ (min (β/6) (ν/2)),lt_min hp₀ (lt_min (by positivity) (by positivity)),
    (min_le_left _ _).trans hp₀1,?_⟩
  intro p hp hpp d hd
  have hpp₀:=hpp.trans (min_le_left _ _)
  have hp1:=hpp₀.trans hp₀1
  have hpβ:p≤β/6:=(hpp.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hpν:p≤ν/2:=(hpp.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hp3:p^3≤p:=by
    have h:=pow_le_pow_left₀ hp.le hp1 2
    have hh:=mul_le_mul_of_nonneg_right h hp.le
    nlinarith only [hh]
  obtain ⟨n₀,hn₀⟩:=hfinish p hp hpp₀ (3*d)
  refine ⟨n₀,?_⟩
  intro V U Gamma Color J I _ _ _ _ _ _ _ _ _ _ hn P π σ H X Z hX hH hsep E T tail head ktail khead
    Qext root hub hroot hhub hroots hhubs M₀ M₁ hM₀ hM₁ hM₀₁ hinner hArcs hSpokes
    C D₁ σ' H' A₀ A₁ X₀ X₁ Y₀ Y₁ Y hD₁ F Q K hcross havoid hdegree
  let incoming:=fun j:J=>markedDeletedEndpointArcEmbedding P π d X true (root j) σ (markedPackingRimGraph (M₀∪M₁)).edgeFinset
  let outgoing:=fun j:J=>markedDeletedEndpointArcEmbedding P π d X false (root j) σ (markedPackingRimGraph (M₀∪M₁)).edgeFinset
  have hin:=fun j a=>marked_deleted_endpoint_embedding_endpoints_type P π d X true (root j) σ (markedPackingRimGraph (M₀∪M₁)).edgeFinset a
  have hout:=fun j a=>marked_deleted_endpoint_embedding_endpoints_type P π d X false (root j) σ (markedPackingRimGraph (M₀∪M₁)).edgeFinset a
  have hnIn (j:J) (a:A₀ j⊕A₁ j):Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming j a))∉(M₀∪M₁).biUnion markedWheelPhysicalResources:=
    marked_deleted_endpoint_avoids_packing P π d (l+4) σ H X true (root j) (M₀∪M₁) a
  have hnOut (j:J) (a:X₀ j⊕X₁ j):Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing j a))∉(M₀∪M₁).biUnion markedWheelPhysicalResources:=
    marked_deleted_endpoint_avoids_packing P π d (l+4) σ H X false (root j) (M₀∪M₁) a
  have hsp:=marked_remaining_spokes_exact H (M₀∪M₁) X Z hSpokes
  have hnRoot (j:J) (u:U) (hu:u∈Y₀ j∪Y₁ j):Sum.inr (root j,u)∉(M₀∪M₁).biUnion markedWheelPhysicalResources:=
    ((hsp.1 (root j) (hroot j) u).mp hu).2
  have hnHub (i:I) (v:V) (hv:v∈Y i):Sum.inr (v,hub i)∉(M₀∪M₁).biUnion markedWheelPhysicalResources:=
    ((hsp.2 (hub i) (hhub i) v).mp hv).2
  have hsub₀:M₀.biUnion markedWheelPhysicalResources⊆(M₀∪M₁).biUnion markedWheelPhysicalResources:=by simp only [Finset.union_biUnion];exact Finset.subset_union_left
  have hsub₁:M₁.biUnion markedWheelPhysicalResources⊆(M₀∪M₁).biUnion markedWheelPhysicalResources:=by simp only [Finset.union_biUnion];exact Finset.subset_union_right
  have hnoD (a:E⊕T) (ha:Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉(M₀∪M₁).biUnion markedWheelPhysicalResources):
      Sum.elim (fun e=>¬D₁.Adj (Sum.inl (tail e)) (Sum.inl (head e)))
        (fun e=>¬D₁.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))) a:=by
    have hc:Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉(markedPackingRimGraph M₁).edgeFinset:=
      fun he=>ha (hsub₁ ((marked_packing_arc_coordinate_iff P π d (l+4) σ H M₁ a).mp he))
    cases a <;> simpa only [Sum.elim_inl,Sum.elim_inr,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,D₁,ordinaryPhysicalGraph] using hc
  have hmem (b incoming:Bool) (j:J) (v:V) (hv:v∈markedEndpointLabels P π d X (b,incoming,root j) σ'):
      v∈X∧¬PermutationClose π (3*d) v (root j):=by
    cases b
    · exact marked_endpoint_label_membership P π d X incoming (root j) σ' (Sum.inl ⟨v,hv⟩)
    · exact marked_endpoint_label_membership P π d X incoming (root j) σ' (Sum.inr ⟨v,hv⟩)
  have hA (j:J) (v:V) (hv:v∈A₀ j∪A₁ j):v∈X∧¬PermutationClose π (3*d) v (root j):=by
    rcases Finset.mem_union.mp hv with hv|hv
    · exact hmem false true j v hv
    · exact hmem true true j v hv
  have hOut (j:J) (v:V) (hv:v∈X₀ j∪X₁ j):v∈X∧¬PermutationClose π (3*d) v (root j):=by
    rcases Finset.mem_union.mp hv with hv|hv
    · exact hmem false false j v hv
    · exact hmem true false j v hv
  have hn0:0≤(Fintype.card (V⊕U):ℝ):=Nat.cast_nonneg _
  have hsmall:p^3*Fintype.card (V⊕U)≤β*Fintype.card (V⊕U)/6:=by
    have hh:=mul_le_mul_of_nonneg_right (hp3.trans hpβ) hn0
    linarith only [hh]
  have hloss:p^3*Fintype.card (V⊕U)≤ν*Fintype.card (V⊕U)/2:=by
    have hh:=mul_le_mul_of_nonneg_right (hp3.trans hpν) hn0
    linarith only [hh]
  exact hn₀ V U E T J I hn tail head ktail khead (H false) (H true) π X Qext
    (by omega) (markedSampleArc_physical_injective P π (3*d) _) hX root hroot
    A₀ A₁ X₀ X₁ Y₀ Y₁ Q incoming outgoing
    (fun j a=>(hin j a).2.1) (fun j a=>(hin j a).1)
    (fun j a=>(hout j a).1) (fun j a=>(hout j a).2.1)
    (fun j a=>(hin j a).2.2) (fun j a=>(hout j a).2.2)
    (fun j v hv=>(hA j v hv).1) (fun j v hv=>(hOut j v hv).1)
    (fun j v hv=>(hA j v hv).2) (fun j v hv=>(hOut j v hv).2)
    (fun j u hu=>(Finset.mem_filter.mp hu).2.1) (fun j u hu=>(Finset.mem_filter.mp hu).2.1)
    Z (fun j v hv=>by rcases Finset.mem_union.mp hv with hv|hv <;> exact (Finset.mem_filter.mp hv).1)
    hub hhub Y (fun i v hv=>(Finset.mem_filter.mp hv).1) F
    (fun i=>hsep (hub i)) hcross hdegree M₀ M₁ hM₀ hM₁ hM₀₁ hinner
    (fun j a he=>hnIn j a (hsub₀ he)) (fun j a he=>hnOut j a (hsub₀ he))
    (fun j u hu he=>hnRoot j u hu (hsub₀ he)) (fun i v hv he=>hnHub i v hv (hsub₀ he))
    D₁ rfl (p^3*Fintype.card (V⊕U)) (by positivity) hD₁
    (fun j=>havoid (Sum.inr j)) (fun i=>havoid (Sum.inl i))
    (fun j u hu he=>hnRoot j u hu (hsub₁ ((marked_packing_spoke_adj_iff H M₁ _ _).mp he)))
    (fun i v hv he=>hnHub i v hv (hsub₁ ((marked_packing_spoke_adj_iff H M₁ _ _).mp he)))
    (fun j a=>hnoD _ (hnIn j a)) (fun j a=>hnoD _ (hnOut j a)) hsmall hloss hroots hhubs
    (fun j a he hn=>marked_deleted_endpoint_exhausts_packing P π d (l+4) σ H X true (root j) (hroot j) (M₀∪M₁) hArcs a he hn)
    (fun j a he hn=>marked_deleted_endpoint_exhausts_packing P π d (l+4) σ H X false (root j) (hroot j) (M₀∪M₁) hArcs a he hn)
    (fun j u hH hn=>(hsp.1 (root j) (hroot j) u).mpr ⟨hH,hn⟩)
    (fun i v hH hn=>(hsp.2 (hub i) (hhub i) v).mpr ⟨hH,hn⟩) hH
end Oberwolfach
