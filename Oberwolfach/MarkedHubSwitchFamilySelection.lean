module

public import Oberwolfach.MarkedHubSwitchResources
public import Oberwolfach.FiniteConflictSeparatedChoices

@[expose] public section

/-! Simultaneous disjoint hub switches. The single-switch construction is
applied after the previously chosen rows and their conflict neighbours are
excluded; roots are retained. All physical disjointness follows through
the original representation, even if the maps on hubs are not injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V U E K W:Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [DecidableEq U] [DecidableEq W]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

 theorem marked_hub_switch_family_selection
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (R:W→Finset (Finset V⊕(V×U))) (Z:I→Finset V) (u u':I→U) (B₀:Finset V)
    (hZ:∀ i,Z i⊆B₀) (hZZ:∀ i j,i≠j→Disjoint (Z i) (Z j))
    (d:ℕ) (F:SimpleGraph V) (D:ℝ) (hD:0≤D) (hF:∀ v,(F.degree v:ℝ)≤D)
    (hchoose:∀ i,∀ B:Finset V,(B.card:ℝ)≤B₀.card+Fintype.card I*d*(D+1)→Disjoint (Z i) B→
      ∃ Y:Finset V,∃ P N:Finset (Finset V⊕(V×U)),
        Disjoint Y (Z i∪B)∧Y.card=d∧(∀ x∈Y,∀ y∈Y,¬F.Adj x y)∧
        HasResourceDecomposition R P∧HasResourceDecomposition R N∧
        (∀ e∈P∪N,MarkedSwitchResource tail head ktail khead π Y (Z i) (u i) (u' i) e)∧
        ∀ e,(if e∈P then (1:ℤ) else 0)-(if e∈N then 1 else 0)=
          (if e∈(Z i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
          (if e∈(Z i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0)):
    ∃ Y:I→Finset V,∃ P N:I→Finset (Finset V⊕(V×U)),
      (∀ i,Disjoint (Y i) B₀∧(Y i).card=d∧(∀ x∈Y i,∀ y∈Y i,¬F.Adj x y)∧
        HasResourceDecomposition R (P i)∧HasResourceDecomposition R (N i)∧
        (∀ e∈P i∪N i,MarkedSwitchResource tail head ktail khead π (Y i) (Z i) (u i) (u' i) e)∧
        ∀ e,(if e∈P i then (1:ℤ) else 0)-(if e∈N i then 1 else 0)=
          (if e∈(Z i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
          (if e∈(Z i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0))∧
      (∀ i j,i≠j→Disjoint (Y i∪Z i) (Y j∪Z j)∧
        (∀ x∈Y i,∀ y∈Y j,¬F.Adj x y)∧Disjoint (P i∪N i) (P j∪N j)):=by
  let C:=Finset V×Finset (Finset V⊕(V×U))×Finset (Finset V⊕(V×U))
  let Good:I→C→Prop:=fun i c=>
    c.1.card=d∧(∀ x∈c.1,∀ y∈c.1,¬F.Adj x y)∧
      HasResourceDecomposition R c.2.1∧HasResourceDecomposition R c.2.2∧
      (∀ e∈c.2.1∪c.2.2,MarkedSwitchResource tail head ktail khead π c.1 (Z i) (u i) (u' i) e)∧
      ∀ e,(if e∈c.2.1 then (1:ℤ) else 0)-(if e∈c.2.2 then 1 else 0)=
        (if e∈(Z i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
        (if e∈(Z i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0)
  have hex:∀ i,∀ B:Finset V,(B.card:ℝ)≤B₀.card+Fintype.card I*d*(D+1)→
      ∃ c:C,Good i c∧c.1.card≤d∧Disjoint c.1 B:=by
    intro i B hB
    have hBc:((B\Z i).card:ℝ)≤B₀.card+Fintype.card I*d*(D+1):=
      (Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)).trans hB
    have hdis:Disjoint (Z i) (B\Z i):=by
      apply Finset.disjoint_left.mpr
      intro v hv hv';exact (Finset.mem_sdiff.mp hv').2 hv
    obtain ⟨Y,P,N,hY,hc,hF,hP,hN,hs,hi⟩:=hchoose i (B\Z i) hBc hdis
    refine ⟨(Y,P,N),⟨hc,hF,hP,hN,hs,hi⟩,hc.le,hY.mono_right ?_⟩
    intro v hv
    by_cases hz:v∈Z i
    · exact Finset.mem_union_left _ hz
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv,hz⟩)
  obtain ⟨f,hf,hd⟩:=finite_conflict_separated_choices (fun c:C=>c.1) Good B₀ d F D hD hF hex
  refine ⟨fun i=>(f i).1,fun i=>(f i).2.1,fun i=>(f i).2.2,?_,?_⟩
  · intro i
    exact ⟨(hf i).2.2,(hf i).1⟩
  · intro i j hij
    have hYY:Disjoint (f i).1 (f j).1:=(hd i j hij).1
    have hYZ:Disjoint (f i).1 (Z j):=(hf i).2.2.mono_right (hZ j)
    have hZY:Disjoint (Z i) (f j).1:=((hf j).2.2.mono_right (hZ i)).symm
    have hT:Disjoint ((f i).1∪Z i) ((f j).1∪Z j):=by
      rw [Finset.disjoint_union_left,Finset.disjoint_union_right,Finset.disjoint_union_right]
      exact ⟨⟨hYY,hYZ⟩,⟨hZY,hZZ i j hij⟩⟩
    refine ⟨hT,(hd i j hij).2,?_⟩
    exact marked_resource_sets_disjoint hp _ _ hT _ _
      (fun e he=>marked_switch_resource_supported _ _ _ _ e ((hf i).1.2.2.2.2.1 e he))
      (fun e he=>marked_switch_resource_supported _ _ _ _ e ((hf j).1.2.2.2.2.1 e he))

end Oberwolfach
