module

public import Oberwolfach.MarkedFiniteDeletionDegrees

@[expose] public section

/-! The reserved inner graph costs at most the size of the inner part in
each physical degree. Add the proved degrees of the prescribed packing;
no auxiliary-degree estimate is silently used as a physical one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_packing_deletion_bounds
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (I:Finset V) (J:Finset U) (hI:∀ x,π x∈I↔x∈I):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (KA:Finset (E₀⊕E₁)) (KS:Finset (V×U)),
    (∀ a∈KA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ z∈KS,z.1∈I∧z.2∈J)→
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    ∀ cR cV cU:ℝ,
    (∀ x,((markedPackingRimGraph M).degree x:ℝ)≤cR)→
    (∀ x,((Finset.univ.filter (markedPackingSpokes M x)).card:ℝ)≤cV)→
    (∀ u,((Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card:ℝ)≤cU)→
    let DR:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)
    let DS:=markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)
    (∀ x,(DR.degree x:ℝ)≤I.card+cR) ∧
    (∀ x,(DS.degree (Sum.inl x):ℝ)≤J.card+cV) ∧
    (∀ u,(DS.degree (Sum.inr u):ℝ)≤I.card+cU):=by
  intro E₀ E₁ tail head ktail khead KA KS hKA hKS M cR cV cU hR hV hU
  have hphys (a:E₀⊕E₁) (ha:a∈KA):markedPhysicalEdge tail head ktail khead π a⊆I:=by
    have hh:=hKA a ha
    cases a with
    | inl a=>exact by simpa only [markedPhysicalEdge,Sum.elim_inl,Sum.elim_inr,Finset.insert_subset_iff,Finset.singleton_subset_iff] using hh
    | inr a=>exact by simpa only [markedPhysicalEdge,Sum.elim_inl,Sum.elim_inr,Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro hh.1 ((hI _).mpr hh.2)
  have hKR (x:V):(markedSampleArcSetGraph P π d σ KA).degree x≤I.card:=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨a,ha,he⟩:=Finset.mem_image.mp (((markedSampleArcSetGraph P π d σ KA).mem_neighborFinset x y).mp hy).2
    apply hphys a ha
    rw [he]
    simp
  have hKV (x:V):(markedFiniteSpokeGraph KS).degree (Sum.inl x)≤J.card:=by
    rw [markedFiniteSpokeGraph_degree_row]
    exact Finset.card_le_card (fun u hu=>(hKS (x,u) (Finset.mem_filter.mp hu).2).2)
  have hKU (u:U):(markedFiniteSpokeGraph KS).degree (Sum.inr u)≤I.card:=by
    rw [markedFiniteSpokeGraph_degree_col]
    exact Finset.card_le_card (fun x hx=>(hKS (x,u) (Finset.mem_filter.mp hx).2).1)
  dsimp only
  rw [markedSampleArcSetGraph_union,markedSampleArcSetGraph_packing,markedFiniteSpokeGraph_union]
  obtain ⟨hMR,hMC⟩:=markedFiniteSpokeGraph_packing_degrees M
  refine ⟨?_,?_,?_⟩
  · intro x
    have hg:=(Nat.cast_le (α:=ℝ)).mpr (graph_degree_sup_le (markedSampleArcSetGraph P π d σ KA) (markedPackingRimGraph M) x)
    have hk:(↑((markedSampleArcSetGraph P π d σ KA).degree x):ℝ)≤I.card:=Nat.cast_le.mpr (hKR x)
    push_cast at hg
    simpa only [←SimpleGraph.ncard_neighborSet] using hg.trans (add_le_add hk (hR x))
  · intro x
    have hg:=(Nat.cast_le (α:=ℝ)).mpr (graph_degree_sup_le (markedFiniteSpokeGraph KS)
      (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)) (Sum.inl x))
    have hk:(↑((markedFiniteSpokeGraph KS).degree (Sum.inl x)):ℝ)≤J.card:=Nat.cast_le.mpr (hKV x)
    rw [hMR] at hg
    push_cast at hg
    simpa only [←SimpleGraph.ncard_neighborSet] using hg.trans (add_le_add hk (hV x))
  · intro u
    have hg:=(Nat.cast_le (α:=ℝ)).mpr (graph_degree_sup_le (markedFiniteSpokeGraph KS)
      (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)) (Sum.inr u))
    have hk:(↑((markedFiniteSpokeGraph KS).degree (Sum.inr u)):ℝ)≤I.card:=Nat.cast_le.mpr (hKU u)
    rw [hMC] at hg
    push_cast at hg
    simpa only [←SimpleGraph.ncard_neighborSet] using hg.trans (add_le_add hk (hU u))

end Oberwolfach
