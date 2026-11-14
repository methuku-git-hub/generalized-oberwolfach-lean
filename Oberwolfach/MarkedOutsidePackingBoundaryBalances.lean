module

public import Oberwolfach.MarkedOutsidePackingRemainder
public import Oberwolfach.MarkedRemainingBoundaryBalances
public import Oberwolfach.MarkedFiniteDeletionDegrees

@[expose] public section

/-! Boundary endpoint balances and hub ratios are consequences of the
actual outside packing, rather than additional assumptions on its output. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_outside_packing_boundary_balances
    {V U Gamma Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Gamma] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Gamma Color)
    (H:Bool→V→U→Prop) (hH:∀ x u,¬(H false x u∧H true x u)) (X:Finset V) (Z:Finset U):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
    (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources)→
    (∀ x u,x∉X→u∉Z→H false x u∨H true x u→Sum.inr (x,u)∈M.biUnion markedWheelPhysicalResources)→
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ
      (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)) m→
    let DR:=markedPackingRimGraph M
    let DS:=ordinaryPhysicalGraph DR (markedPackingSpokes M)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS;
    (∀ v,v∉X→
      let A₀:=markedEndpointLabels P π d X (false,true,v) σ'
      let A₁:=markedEndpointLabels P π d X (true,true,v) σ'
      let X₀:=markedEndpointLabels P π d X (false,false,v) σ'
      let X₁:=markedEndpointLabels P π d X (true,false,v) σ'
      let Y₀:=Z.filter (H' false v)
      let Y₁:=Z.filter (H' true v);
      Disjoint Y₀ Y₁∧A₀.card+A₁.card=Y₀.card+Y₁.card∧
      X₀.card+X₁.card=Y₀.card+Y₁.card∧A₁.card=Y₁.card) ∧
    (∀ u,u∉Z→
      let Y:=X.filter (fun x=>(H false x u∨H true x u)∧¬DS.Adj (Sum.inl x) (Sum.inr u));
      (Y.filter (H false · u)).card=m*(Y.filter (H true · u)).card):=by
  intro E K tail head ktail khead M hM hArcs hSpokes hdiv DR DS σ' H'
  have hp:Function.Injective (markedPhysicalEdge tail head ktail khead π):=
    markedSampleArc_physical_injective P π (3*d) _
  have hr:=marked_outside_packing_remainder hp hH X Z M hM hArcs hSpokes hdiv
  let A:=Finset.univ.filter (fun a:E⊕K=>
    Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉DR.edgeFinset)
  let S:=Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧¬DS.Adj (Sum.inl z.1) (Sum.inr z.2))
  have hA:A=Finset.univ\M.biUnion markedWheelArcs:=by
    change (Finset.univ.filter (fun a:E⊕K=>
      Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉(markedPackingRimGraph M).edgeFinset))=_
    rw [←markedSampleArcSetGraph_packing P π d m σ H M]
    exact markedSampleArcSetGraph_remaining P π d σ _
  have hS:S=(Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2))\M.biUnion markedWheelSpokePairs:=by
    ext z
    have hs:z∈M.biUnion markedWheelSpokePairs↔markedPackingSpokes M z.1 z.2:=by
      rw [←markedPackingResources_spoke]
      simp only [Finset.mem_biUnion,markedWheel_spoke_resource]
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,DS,ordinaryPhysicalGraph,hs]
  have hd:MarkedRemainderDivisible tail head ktail khead (H true) A S m:=by
    rw [hA,hS]
    exact hr.1
  constructor
  · intro v hv
    apply marked_remaining_boundary_row_balances P π d m σ H DR DS X Z v (hH v)
    · exact hd
    · intro a ha he
      change Sum.elim head khead a=v at he
      apply hr.2.2.1 a (hA ▸ ha)
      simpa only [he] using hv
    · intro a ha he
      change Sum.elim tail ktail a=v at he
      apply hr.2.1 a (hA ▸ ha)
      simpa only [he] using hv
    · intro u hu
      exact hr.2.2.2.1 (v,u) (hS ▸ hu) hv
  · intro u hu
    apply marked_remaining_boundary_hub_ratio H DS X u m (fun x=>hH x u)
    · exact hd.hub u
    · intro x hx
      exact hr.2.2.2.2 (x,u) (hS ▸ hx) hu
end Oberwolfach
