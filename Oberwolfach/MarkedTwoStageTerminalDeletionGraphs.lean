module

public import Oberwolfach.MarkedTwoStageActiveSpokeGraphs
public import Oberwolfach.MarkedReservedFirstDeletionProtection
public import Oberwolfach.MarkedPackingResourceDetermination
public import Oberwolfach.MarkedReservedAbsorberAdaptiveDeletion

@[expose] public section
/-! If the final pair lies in the active pair, a preselected absorber
continues to absorb every divisible terminal remainder after both packings. -/
set_option autoImplicit false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_two_stage_terminal_deletion_graphs
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ₀:RawMarkedOutcome V U Γ Color) (H₀:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (Xterm:Finset V) (Zterm:Finset U)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hpriorR:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬FR.Adj x y)
    (hpriorS:∀ v u,Sum.inr (v,u)∈C→¬FS.Adj (Sum.inl v) (Sum.inr u))
    (hpriorTerm:∀ v∈Xterm,∀ u∈Zterm,¬FS.Adj (Sum.inl v) (Sum.inr u))
    (I T:Finset V) (J W:Finset U) (hI:∀ x,π x∈I↔x∈I)
    (hX:Xterm⊆I\T) (hZ:Zterm⊆J\W) (hC:∀ e∈C,¬markedInnerResource I J e):
    let σ:=rawMarkedDeleteRims σ₀ FR.edgeFinset
    let H:=markedDeletePhysicalSpokes H₀ FS
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ (A₀:Finset (E⊕K)) (S₀:Finset (V×U))
      (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)))
      (R:Finset (Finset V⊕(V×U))),
    (∀ a∈A₀,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ z∈S₀,z.1∈I∧z.2∈J)→
    Disjoint C (M.biUnion markedWheelPhysicalResources)→
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=R.filter (markedStarResource T W)→
    let Astar:=A₀.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let Sstar:=S₀.filter (fun z=>z.1∈T∨z.2∈W)
    let DR₁:=markedSampleArcSetGraph P π d σ (Astar∪M.biUnion markedWheelArcs)
    let DS₁:=markedFiniteSpokeGraph (Sstar∪M.biUnion markedWheelSpokePairs)
    let σ₁:=rawMarkedDeleteRims σ DR₁.edgeFinset
    let H₁:=markedDeletePhysicalSpokes H DS₁
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ₁ (Sum.inl e)) false
    let K₁:=MarkedSampleArc P π (3*d) (fun e=>σ₁ (Sum.inl e)) true;
    ∀ N:Finset (MarkedWheel (fun e:E₁=>e.val.1) (fun e=>e.val.2)
      (fun e:K₁=>e.val.1) (fun e=>e.val.2) m π (3*d) (H₁ false) (H₁ true)),
    Disjoint C (N.biUnion markedWheelPhysicalResources)→
    (N.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅→
    let DR₂:=markedPackingRimGraph N
    let DS₂:=markedFiniteSpokeGraph (N.biUnion markedWheelSpokePairs)
    let DR:=FR⊔(DR₁⊔DR₂)
    let DS:=FS⊔(DS₁⊔DS₂)
    (∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬DR.Adj x y)∧
    (∀ v u,Sum.inr (v,u)∈C→¬DS.Adj (Sum.inl v) (Sum.inr u))∧
    (∀ v∈Xterm,∀ u∈Zterm,¬DS.Adj (Sum.inl v) (Sum.inr u)):=by
  intro σ H E K tail head ktail khead A₀ S₀ M R hA₀ hS₀ hMC hM Astar Sstar DR₁ DS₁ σ₁ H₁ E₁ K₁ N hNC hN DR₂ DS₂ DR DS
  have hAstar:∀ a∈Astar,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I:=fun a ha=>hA₀ a (Finset.mem_filter.mp ha).1
  have hSstar:∀ z∈Sstar,z.1∈I∧z.2∈J:=fun z hz=>hS₀ z (Finset.mem_filter.mp hz).1
  have hfirst:=marked_first_deletion_preserves_reserved_resources P π d m σ H C I J hI hC Astar Sstar M hAstar hSstar hMC
  have hsecondR:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬DR₂.Adj x y:=by
    intro x y hc hxy
    have hr:({x,y}:Finset V)∈markedPackingRims N:=hxy.2
    exact Finset.disjoint_left.mp hNC hc ((markedPackingResources_rim N _).mpr hr)
  have hsecondS:∀ v u,Sum.inr (v,u)∈C→¬DS₂.Adj (Sum.inl v) (Sum.inr u):=by
    intro v u hc huv
    have hz:(v,u)∈N.biUnion markedWheelSpokePairs:=(markedFiniteSpokeGraph_adj _ v u).mp huv
    have hr:Sum.inr (v,u)∈N.biUnion markedWheelPhysicalResources:=by
      rw [←markedPackingResources_eq_finite _ _ _ _ π N]
      exact (markedFiniteResources_spoke _ _ _ _ π _ _ (v,u)).mpr hz
    exact Finset.disjoint_left.mp hNC hc hr
  have hactive:=marked_two_stage_deletion_spoke_graphs_avoid_active_pair I T J W S₀ M R hM N hN
  have hR:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬DR.Adj x y:=by
    intro x y hc
    simpa only [DR,SimpleGraph.sup_adj,not_or] using ⟨hpriorR x y hc,hfirst.1 x y hc,hsecondR x y hc⟩
  have hS:∀ v u,Sum.inr (v,u)∈C→¬DS.Adj (Sum.inl v) (Sum.inr u):=by
    intro v u hc
    simpa only [DS,SimpleGraph.sup_adj,not_or] using ⟨hpriorS v u hc,hfirst.2.1 v u hc,hsecondS v u hc⟩
  have hTerm:∀ v∈Xterm,∀ u∈Zterm,¬DS.Adj (Sum.inl v) (Sum.inr u):=by
    intro v hv u hu
    have hh:=hactive v (hX hv) u (hZ hu)
    simpa only [DS,SimpleGraph.sup_adj,not_or] using ⟨hpriorTerm v hv u hu,hh.1,hh.2⟩
  exact ⟨hR,hS,hTerm⟩
end Oberwolfach
