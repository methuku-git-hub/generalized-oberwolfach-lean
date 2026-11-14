module

public import Oberwolfach.MarkedUniformHostTransformer
public import Oberwolfach.MarkedRootPairBaseExtension
public import Oberwolfach.MarkedSupportedResourceFamilies
public import Oberwolfach.FiniteSeparatedRowHubChoices

@[expose] public section

/-! Joint marked transformers from the fixed original common-cycle
profiles. Only bounded added row sets are enlarged by permutation
neighbourhoods; the linear forbidden allowance is not multiplied by b. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 50000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_uniform_transformer_family (l:ℕ) (hl:2≤l)
    (ρ σ q₀ β blo bhi:ℝ) (hρ:0<ρ) (hσ:0<σ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ r e k:ℕ,∃ a₀ b₀:ℕ,∀ f b:ℕ,∀ dF:ℝ,0≤dF→∃ N:ℕ,
    ∀ (V U E K A S:Type) [Fintype V] [Fintype U] [Fintype A] [Fintype S]
      [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S],
    N≤Fintype.card V→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),1≤b→
    ∀ (P:Fin k→MarkedRootPair tail head ktail khead H₀ HK π b (l+4) A S) (W Z:Finset V) (B:Finset U),
    Z.card≤r→(∀ i,(P i).R∪(P i).R'⊆Z)→(∀ i,(P i).B=B)→Fintype.card A+Fintype.card S≤e→
    MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l (ρ*Fintype.card V) (σ*Fintype.card V)→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    (B.card:ℝ)≤ε*Fintype.card V+f→(W.card:ℝ)≤ε*Fintype.card V+f→
    ∀ F:SimpleGraph V,permutationConflictGraph π b≤F→
    (∀ v z,HK v z→¬H₀ v z)→(∀ v,(F.degree v:ℝ)≤dF)→
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε→
    ∃ C:Fin k→MarkedSupportedEdgeSet tail head ktail khead π U,
      (∀ i,(C i).rows.card≤a₀∧(C i).hubs.card≤b₀∧
        IsResourceTransformer (fun D:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources D)
          (P i).source (P i).image (C i).edges∧
        (∀ v∈(C i).rows,v∈W→v∈Z)∧
        (∀ u∈(C i).hubs,u∈B→∃ s:S,(P i).u s=u∨(P i).u' s=u)∧
        (∀ e∈(C i).edges,¬MarkedOldResource tail head ktail khead π (W∪Z) B e)∧
        (∀ v∈(C i).rows\Z,∀ z∈Z,¬PermutationClose π b v z)∧
        (∀ v∈(C i).rows\Z,∀ w∈(C i).rows\Z,v≠w→¬PermutationClose π b v w))∧
      (∀ i j,i≠j→Disjoint (C i).edges (C j).edges)∧
      ∀ i j,i≠j→∀ v∈(C i).rows\Z,∀ w∈(C j).rows\Z,¬PermutationClose π b v w:=by
  obtain ⟨ε,hε,hchoose⟩:=marked_uniform_host_transformer l hl ρ σ q₀ β blo bhi hρ hσ hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro r e k
  obtain ⟨a₀,b₀,hchoose⟩:=hchoose r e
  refine ⟨a₀,b₀,?_⟩
  intro f b dF hdF
  let f':=f+(r+k*a₀)*(2*b+1)+k*b₀
  obtain ⟨N,hchoose⟩:=hchoose f' b dF hdF
  refine ⟨N,?_⟩
  intro V U E K A S _ _ _ _ _ _ _ _ hn tail head ktail khead H₀ HK π hb P W Z B hZ hroots hPB he Q hp hB hW F hconf htypes hF Profiles
  let Good:Fin k→MarkedSupportedEdgeSet tail head ktail khead π U→Prop:=fun i C=>
      C.rows.card≤a₀∧C.hubs.card≤b₀∧
      IsResourceTransformer (fun D:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources D)
        (P i).source (P i).image C.edges∧
      (∀ v∈C.rows,v∈W→v∈Z)∧
      (∀ u∈C.hubs,u∈B→∃ s:S,(P i).u s=u∨(P i).u' s=u)∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π (W∪Z) B e)∧
      (∀ v∈C.rows\Z,∀ z∈Z,¬PermutationClose π b v z)∧
      (∀ v∈C.rows\Z,∀ w∈C.rows\Z,v≠w→¬PermutationClose π b v w)
  have chooseOne:∀ Z':Finset V,∀ B':Finset U,(∅:Finset V)⊆Z'→(∅:Finset U)⊆B'→
      Z'.card≤0+Fintype.card (Fin k)*a₀→B'.card≤0+Fintype.card (Fin k)*b₀→∀ i:Fin k,
      ∃ C,Good i C∧(C.rows\Z).card≤a₀∧(C.hubs\B).card≤b₀∧Disjoint (C.rows\Z) Z'∧Disjoint (C.hubs\B) B'∧
        ∀ v∈C.rows\Z,∀ w∈Z',¬PermutationClose π b v w:=by
    intro Z' B' _ _ hZ' hB' i
    have hz:Z'.card≤k*a₀:=by simpa using hZ'
    have hb':B'.card≤k*b₀:=by simpa using hB'
    let close:=markedCloseSet π b (Z∪Z')
    let W':=W∪close
    let BB:=B∪B'
    have hclose:close.card≤(r+k*a₀)*(2*b+1):=
      (markedCloseSet_card π b _).trans (Nat.mul_le_mul_right _ ((Finset.card_union_le _ _).trans (Nat.add_le_add hZ hz)))
    have hW':(W'.card:ℝ)≤ε*Fintype.card V+f':=by
      have hh:(W'.card:ℝ)≤W.card+close.card:=by exact_mod_cast Finset.card_union_le W close
      have hc:(close.card:ℝ)≤(r+k*a₀)*(2*b+1):=by exact_mod_cast hclose
      dsimp only [f'];push_cast
      have hbnon:0≤(k:ℝ)*b₀:=by positivity
      linarith only [hh,hc,hW,hbnon]
    have hBB:(BB.card:ℝ)≤ε*Fintype.card V+f':=by
      have hh:(BB.card:ℝ)≤B.card+B'.card:=by exact_mod_cast Finset.card_union_le B B'
      have hc:(B'.card:ℝ)≤k*b₀:=by exact_mod_cast hb'
      dsimp only [f'];push_cast
      have hn:0≤((r:ℝ)+k*a₀)*(2*b+1):=by positivity
      linarith only [hh,hc,hB,hn]
    let P':=(P i).enlargeBase BB (by rw [hPB];exact Finset.subset_union_left)
    have hr:(P'.R∪P'.R').card≤r:=(Finset.card_le_card (hroots i)).trans hZ
    obtain ⟨X,T,H,hXc,hHc,hroot,hXW,hXZ,hXX,hT,hTs,hTo,hTh,hHold⟩:=hchoose V U E K A S hn
      tail head ktail khead H₀ HK π hb P' W' hr he Q hp hBB hW' F hconf htypes hF Profiles
    have hWZ:W∪Z⊆W':=by
      apply Finset.union_subset Finset.subset_union_left
      intro v hv
      exact Finset.mem_union_right _ (subset_markedCloseSet π b (Z∪Z') (Finset.mem_union_left _ hv))
    have hfree:∀ v∈X\Z,v∈X\(P'.R∪P'.R'):=by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1,fun hh=>(Finset.mem_sdiff.mp hv).2 (hroots i hh)⟩
    have hsep:∀ v∈X\Z,∀ z∈Z∪Z',¬PermutationClose π b v z:=by
      intro v hv z hz hc
      exact Finset.disjoint_left.mp hXW (hfree v hv)
        (Finset.mem_union_right _ (mem_markedCloseSet π b (Z∪Z') hz hc))
    have havoid:∀ e∈T,¬MarkedOldResource tail head ktail khead π (W∪Z) B e:=by
      have hh:=marked_transformer_avoids_old_rows hp X ∅ (P'.R∪P'.R') W' BB T hXW (by simp)
        (by simpa only [Finset.union_empty] using hTs) hTo
      exact fun e he hold=>hh e he (marked_old_resource_mono hWZ Finset.subset_union_left e hold)
    let C:MarkedSupportedEdgeSet tail head ktail khead π U:={
      rows := X
      hubs := H
      edges := T
      supported := by
        intro e he
        cases e with
        | inl e=>exact hTs _ he
        | inr vu=>exact ⟨hTs _ he,hTh vu.1 vu.2 he⟩}
    refine ⟨C,?_,(Finset.card_le_card Finset.sdiff_subset).trans hXc,(Finset.card_le_card Finset.sdiff_subset).trans hHc,?_,?_,?_⟩
    · refine ⟨hXc,hHc,hT,?_,?_,havoid,?_,?_⟩
      · intro v hv hvW
        by_contra hvZ
        exact Finset.disjoint_left.mp hXW (hfree v (Finset.mem_sdiff.mpr ⟨hv,hvZ⟩)) (Finset.mem_union_left _ hvW)
      · intro u hu huB
        exact hHold u hu (Finset.mem_union_left _ huB)
      · intro v hv z hz;exact hsep v hv z (Finset.mem_union_left _ hz)
      · intro v hv w hw hne;exact hXX v (hfree v hv) w (hfree w hw) hne
    · apply Finset.disjoint_left.mpr
      intro v hv hvZ
      exact hsep v hv v (Finset.mem_union_right _ hvZ) (Or.inl rfl)
    · apply Finset.disjoint_left.mpr
      intro u hu huB'
      obtain ⟨s,hs|hs⟩:=hHold u (Finset.mem_sdiff.mp hu).1 (Finset.mem_union_right _ huB')
      · exact (Finset.mem_sdiff.mp hu).2 (hs ▸ (hPB i ▸ (P i).hubRoots s).1)
      · exact (Finset.mem_sdiff.mp hu).2 (hs ▸ (hPB i ▸ (P i).hubRoots s).2)
    · intro v hv w hw;exact hsep v hv w (Finset.mem_union_right _ hw)
  obtain ⟨C,hC,hdis⟩:=finite_separated_row_hub_choices π b
    (fun _ (C:MarkedSupportedEdgeSet tail head ktail khead π U)=>C.rows\Z)
    (fun _ C=>C.hubs\B) Good ∅ ∅ a₀ b₀ (by simpa only [Finset.card_empty] using chooseOne)
  refine ⟨C,fun i=>(hC i).1,?_,?_⟩
  · intro i j hij
    apply marked_supported_sets_disjoint_of_free hp (C i) (C j) Z B (hdis i j hij).1 (hdis i j hij).2.1
    intro e he hold
    exact (hC i).1.2.2.2.2.2.1 e he (marked_old_resource_mono Finset.subset_union_right (by rfl) e hold)
  · intro i j hij;exact (hdis i j hij).2.2

end Oberwolfach
