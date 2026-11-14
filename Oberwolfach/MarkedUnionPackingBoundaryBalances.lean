module

public import Oberwolfach.MarkedOutsidePackingBoundaryBalances
public import Oberwolfach.MarkedPackingPhysicalUnion

@[expose] public section

/-! The actual boundary classes after the constructed pair of disjoint
packings inherit the three row balances and exact hub ratio. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_union_packing_boundary_balances
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
    ∀ M N:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)),
    (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
    (∀ W∈N,∀ W'∈N,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
    Disjoint (M.biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources)→
    (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources∪N.biUnion markedWheelPhysicalResources)→
    (∀ x u,x∉X→u∉Z→H false x u∨H true x u→Sum.inr (x,u)∈M.biUnion markedWheelPhysicalResources∪N.biUnion markedWheelPhysicalResources)→
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ
      (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)) m→
    let DR:=markedPackingRimGraph M⊔markedPackingRimGraph N
    let DS:=ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M)⊔
      ordinaryPhysicalGraph (markedPackingRimGraph N) (markedPackingSpokes N)
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
      (Y.filter (H false · u)).card=m*(Y.filter (H true · u)).card) :=by
  intro E K tail head ktail khead M N hM hN hMN hArcs hSpokes hdiv
  have hmatch:=marked_packing_union_is_matching M N hM hN hMN
  have hR:∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈(M∪N).biUnion markedWheelPhysicalResources:=by
    simpa only [Finset.union_biUnion] using hArcs
  have hS:∀ x u,x∉X→u∉Z→H false x u∨H true x u→Sum.inr (x,u)∈(M∪N).biUnion markedWheelPhysicalResources:=by
    simpa only [Finset.union_biUnion] using hSpokes
  have h:=marked_outside_packing_boundary_balances P π d m σ H hH X Z (M∪N) hmatch hR hS hdiv
  dsimp only at h ⊢
  have hphys:=markedPackingPhysicalGraph_union M N
  have hrim:=markedPackingRimGraph_union M N
  simp only [hphys] at h
  convert h using 1 <;> try simp only [hrim]
  all_goals congr!
  all_goals exact hrim.symm
end Oberwolfach
