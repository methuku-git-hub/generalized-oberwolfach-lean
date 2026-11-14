module

public import Oberwolfach.MarkedTwoStageReserveAndActiveProtection
public import Oberwolfach.MarkedReservedDeepPackingLift

@[expose] public section
/-! A deep packing from the reserve-deleted host lifts to the first-deleted
host while protecting both the active pair and the selected absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_reserved_lift_protects_active_pair_and_absorber
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m) (hb:1≤3*d)
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
    let RC:=physicalEdgeGraph (markedReservedRimPairs C)
    let SC:=markedFiniteSpokeGraph (markedReservedSpokePairs C);
    ∀ MD:Finset (MarkedPhysicalDeletedSampleWheel P π d m σ' RC SC H'),
    (∀ W∈MD,∀ Z∈MD,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))→
    (MD.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅→
    ∃ N:Finset (MarkedWheel tail' head' ktail' khead' m π (3*d) (H' false) (H' true)),
    (∀ W∈N,∀ Z∈N,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
    N.biUnion markedWheelPhysicalResources=MD.biUnion markedWheelPhysicalResources∧
    Disjoint C (N.biUnion markedWheelPhysicalResources)∧
    let σ'':=rawMarkedDeleteRims σ' (markedPackingRimGraph N).edgeFinset
    let H'':=markedDeletePhysicalSpokes H' (markedFiniteSpokeGraph (N.biUnion markedWheelSpokePairs))
    let E'':=MarkedSampleArc P π (3*d) (fun e=>σ'' (Sum.inl e)) false
    let K'':=MarkedSampleArc P π (3*d) (fun e=>σ'' (Sum.inl e)) true;
    (∀ mark x y,x∈I\T→y∈I\T→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>σ'' (Sum.inl e)) mark x y=1)) ∧
    (∀ j v u,v∈I\T→u∈J\W→(H j v u↔H'' j v u)) ∧
    (∀ e:E,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→∃ e':E'',e'.val=e.val) ∧
    (∀ e:K,Sum.inl ({e.val.1,π e.val.2}:Finset V)∈C→∃ e':K'',e'.val=e.val) ∧
    (∀ b v u,Sum.inr (v,u)∈C→H b v u→H'' b v u):=by
  intro E K tail head ktail khead A₀ S₀ M R hA₀ hS₀ hMdis hM A S FR FS σ' H' E' K' tail' head' ktail' khead' RC SC MD hMD hMDinner
  obtain ⟨N,hN,hres,hdis⟩:=marked_reserved_deleted_packing_lift P π d m hm hb σ' H' C MD hMD
  have hInner:(N.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅:=by
    rw [hres]
    exact hMDinner
  refine ⟨N,hN,hres,hdis,?_⟩
  exact marked_two_stage_cover_protects_reserve_and_active_pair P π d m σ H C I T J W hI hT hC
    A₀ S₀ M R hA₀ hS₀ hMdis hM N hInner hdis
end Oberwolfach
