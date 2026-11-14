module

public import Oberwolfach.MarkedTwoStageCoverActiveProtection
public import Oberwolfach.MarkedReservedFirstDeletionProtection

@[expose] public section
/-! The same two physical deletions preserve both the active pair needed by
the next level and the preselected absorber's typed resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_two_stage_cover_protects_reserve_and_active_pair
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (I T:Finset V) (J W:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T)
    (hC:∀ e∈C,¬markedInnerResource I J e):
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
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      R.filter (markedStarResource T W)→
    let A:=A₀.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let S:=S₀.filter (fun z=>z.1∈T∨z.2∈W)
    let FR:=markedSampleArcSetGraph P π d σ (A∪M.biUnion markedWheelArcs)
    let FS:=markedFiniteSpokeGraph (S∪M.biUnion markedWheelSpokePairs)
    let σ':=rawMarkedDeleteRims σ FR.edgeFinset
    let H':=markedDeletePhysicalSpokes H FS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let tail':=fun e:E'=>e.val.1
    let head':=fun e:E'=>e.val.2
    let ktail':=fun e:K'=>e.val.1
    let khead':=fun e:K'=>e.val.2;
    ∀ MD:Finset (MarkedWheel tail' head' ktail' khead' m π (3*d) (H' false) (H' true)),
    (MD.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅→
    Disjoint C (MD.biUnion markedWheelPhysicalResources)→
    let σ'':=rawMarkedDeleteRims σ' (markedPackingRimGraph MD).edgeFinset
    let H'':=markedDeletePhysicalSpokes H' (markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs))
    let E'':=MarkedSampleArc P π (3*d) (fun e=>σ'' (Sum.inl e)) false
    let K'':=MarkedSampleArc P π (3*d) (fun e=>σ'' (Sum.inl e)) true;
    (∀ mark x y,x∈I\T→y∈I\T→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>σ'' (Sum.inl e)) mark x y=1)) ∧
    (∀ j v u,v∈I\T→u∈J\W→(H j v u↔H'' j v u)) ∧
    (∀ e:E,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→∃ e':E'',e'.val=e.val) ∧
    (∀ e:K,Sum.inl ({e.val.1,π e.val.2}:Finset V)∈C→∃ e':K'',e'.val=e.val) ∧
    (∀ b v u,Sum.inr (v,u)∈C→H b v u→H'' b v u):=by
  intro E K tail head ktail khead A₀ S₀ M R hA₀ hS₀ hMdis hM A S FR FS σ' H' E' K' tail' head' ktail' khead' MD hMD hMDdis σ'' H'' E'' K''
  have hA:∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I:=by
    intro a ha
    exact hA₀ a (Finset.mem_filter.mp ha).1
  have hS:∀ z∈S,z.1∈I∧z.2∈J:=by
    intro z hz
    exact hS₀ z (Finset.mem_filter.mp hz).1
  have hactive:=marked_two_stage_cover_protects_active_pair P π d m σ H I T J W hI hT A₀ S₀ M R hM MD hMD
  have hreserve:=marked_two_stage_deletions_preserve_reserved_resources P π d m σ H C I J hI hC A S M hA hS hMdis MD hMDdis
  exact ⟨hactive.1,hactive.2,hreserve⟩
end Oberwolfach
