module

public import Oberwolfach.MarkedDeletedStarCoverTransport
public import Oberwolfach.MarkedActiveCoverPackingLift
public import Oberwolfach.MarkedFiniteDeletionDegrees

@[expose] public section

/-! The deep cover and the active cover exhaust all original resources
outside the inner pair. The temporary reserved graphs are supported inside
that pair and are never counted as edges removed by a wheel packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_protected_three_stage_coverage
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (I T:Finset V) (J W:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T)
    (KR:SimpleGraph V) (KS:SimpleGraph (V⊕U))
    (hKR:∀ x y,KR.Adj x y→x∈I∧y∈I)
    (hKS:∀ x u,KS.Adj (Sum.inl x) (Sum.inr u)→x∈I∧u∈J):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    ∀ ME MD MU:Finset (MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)),
    let FE:=ME.biUnion markedWheelPhysicalResources
    let FD:=MD.biUnion markedWheelPhysicalResources
    let FU:=MU.biUnion markedWheelPhysicalResources
    let ER:=markedPackingRimGraph ME
    let DR:=markedPackingRimGraph MD
    let ES:=markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs)
    let DS:=markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs);
    (∀ j x y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) j x y=1→
      ¬(KR⊔ER).Adj x (if j then π y else y)→
      markedStarResource T W (Sum.inl ({x,if j then π y else y}:Finset V))→
      Sum.inl ({x,if j then π y else y}:Finset V)∈FD)→
    (∀ j x u,H j x u→¬(KS⊔ES).Adj (Sum.inl x) (Sum.inr u)→
      markedStarResource T W (Sum.inr (x,u))→Sum.inr (x,u)∈FD)→
    (∀ j x y,x∉T→y∉T→markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) j x y=1→
      ¬(ER⊔DR).Adj x (if j then π y else y)→x∉I∨y∉I→
      Sum.inl ({x,if j then π y else y}:Finset V)∈FU)→
    (∀ j x u,x∉T→u∉W→H j x u→¬(ES⊔DS).Adj (Sum.inl x) (Sum.inr u)→x∉I∨u∉J→
      Sum.inr (x,u)∈FU)→
    (∀ a:E⊕K,Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a∉I∨
      Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a∉I→
      Sum.inl (markedPhysicalEdge (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π a)∈FE∪FD∪FU)∧
    (∀ x u,H false x u∨H true x u→x∉I∨u∉J→Sum.inr (x,u)∈FE∪FD∪FU):=by
  intro E K ME MD MU FE FD FU ER DR ES DS hdeepR hdeepS hactiveR hactiveS
  have hrim (j:Bool) (x y:V)
      (hxy:markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) j x y=1)
      (hout:x∉I∨y∉I):(Sum.inl ({x,if j then π y else y}:Finset V)∈FE∨
        Sum.inl ({x,if j then π y else y}:Finset V)∈FD)∨
        Sum.inl ({x,if j then π y else y}:Finset V)∈FU:=by
    let e:Finset V⊕(V×U):=Sum.inl {x,if j then π y else y}
    by_cases he:e∈FE∨e∈FD
    · exact Or.inl he
    have hnotE:e∉FE:=fun h=>he (Or.inl h)
    have hnotD:e∉FD:=fun h=>he (Or.inr h)
    have hER:¬ER.Adj x (if j then π y else y):=by
      intro ha
      exact hnotE ((markedPackingResources_rim ME _).mpr ha.2)
    have hDR:¬DR.Adj x (if j then π y else y):=by
      intro ha
      exact hnotD ((markedPackingResources_rim MD _).mpr ha.2)
    have hKR':¬KR.Adj x (if j then π y else y):=by
      intro ha
      obtain ⟨hx,hy⟩:=hKR x _ ha
      have hy':y∈I:=by cases j <;> simpa only [Bool.false_eq_true,ite_false,ite_true,hI] using hy
      exact hout.elim (fun h=>h hx) (fun h=>h hy')
    have hstar:¬markedStarResource T W e:=by
      intro hs
      exact hnotD (hdeepR j x y hxy (by simpa only [SimpleGraph.sup_adj,not_or] using And.intro hKR' hER) hs)
    have hxT:x∉T:=by
      intro hx
      exact hstar ⟨x,by simp [e,markedStarResource],hx⟩
    have hyT:y∉T:=by
      intro hy
      have hy':(if j then π y else y)∈T:=by cases j <;> simpa only [Bool.false_eq_true,ite_false,ite_true,hT] using hy
      exact hstar ⟨if j then π y else y,by simp [e,markedStarResource],hy'⟩
    exact Or.inr (hactiveR j x y hxT hyT hxy
      (by simpa only [SimpleGraph.sup_adj,not_or] using And.intro hER hDR) hout)
  have hspoke (j:Bool) (x:V) (u:U) (hh:H j x u) (hout:x∉I∨u∉J):(Sum.inr (x,u)∈FE∨Sum.inr (x,u)∈FD)∨Sum.inr (x,u)∈FU:=by
    by_cases he:Sum.inr (x,u)∈FE∨Sum.inr (x,u)∈FD
    · exact Or.inl he
    have hnotE:Sum.inr (x,u)∉FE:=fun h=>he (Or.inl h)
    have hnotD:Sum.inr (x,u)∉FD:=fun h=>he (Or.inr h)
    have hES:¬ES.Adj (Sum.inl x) (Sum.inr u):=by
      intro ha
      obtain ⟨C,hC,heC⟩:=Finset.mem_biUnion.mp ((markedFiniteSpokeGraph_adj _ x u).mp ha)
      exact hnotE (Finset.mem_biUnion.mpr ⟨C,hC,(markedWheel_spoke_resource C (x,u)).mp heC⟩)
    have hDS:¬DS.Adj (Sum.inl x) (Sum.inr u):=by
      intro ha
      obtain ⟨C,hC,heC⟩:=Finset.mem_biUnion.mp ((markedFiniteSpokeGraph_adj _ x u).mp ha)
      exact hnotD (Finset.mem_biUnion.mpr ⟨C,hC,(markedWheel_spoke_resource C (x,u)).mp heC⟩)
    have hKS':¬KS.Adj (Sum.inl x) (Sum.inr u):=by
      intro ha
      have h:=hKS x u ha
      exact hout.elim (fun hn=>hn h.1) (fun hn=>hn h.2)
    have hstar:¬markedStarResource T W (Sum.inr (x,u)):=by
      intro hs
      exact hnotD (hdeepS j x u hh (by simpa only [SimpleGraph.sup_adj,not_or] using And.intro hKS' hES) hs)
    have hxT:x∉T:=fun hx=>hstar (Or.inl hx)
    have huW:u∉W:=fun hu=>hstar (Or.inr hu)
    exact Or.inr (hactiveS j x u hxT huW hh
      (by simpa only [SimpleGraph.sup_adj,not_or] using And.intro hES hDS) hout)
  constructor
  · intro a hout
    cases a with
    | inl a=>simpa only [Finset.mem_union, markedPhysicalEdge, Bool.false_eq_true, ite_false, Sum.elim_inl] using hrim false a.val.1 a.val.2 a.property hout
    | inr a=>simpa only [Finset.mem_union, markedPhysicalEdge, ite_true, Sum.elim_inr] using hrim true a.val.1 a.val.2 a.property hout
  · intro x u hh hout
    simpa only [Finset.mem_union] using hh.elim (fun h=>hspoke false x u h hout) (fun h=>hspoke true x u h hout)

end Oberwolfach
