module

public import Oberwolfach.MarkedPrescribedPackingUnion
public import Oberwolfach.MarkedSparseInnerDomainEdgePacking

@[expose] public section

/-! The sparse inner-edge packing with the tolerance chosen before the
permutation separation radius. The actual free-use cap is ceil(eta*n);
all numerical conditions of both successive constructions are proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sparse_inner_domain_packing (l:ℕ) (hl:2≤l) (β:ℝ) (hβ:0<β)
    (η:ℝ) (hη:0<η) (hη1:η≤1) (hscale:100*((l:ℝ)+20)*η≤β):
    ∀ b:ℕ,1≤b→∃ n₀:ℕ,
    ∀ (V U E T:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head:E→V) (ktail khead:T→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),n₀≤Fintype.card V→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    ∀ (X:Finset V) (Z:Finset U),(∀ v,π v∈X↔v∈X)→
    (∀ u,∀ t x,β*Fintype.card V≤((X.filter (fun z=>markedArcPresent tail head ktail khead t x z∧
      (if t then HK z u else H₀ z u))).card:ℝ))→
    (∀ u,∀ t x y,x≠(if t then π y else y)→β*Fintype.card V≤((X.filter (fun z=>
      markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead t z y∧H₀ z u)).card:ℝ))→
    ∀ Nr Ns:ℕ,(Nr:ℝ)≤η^2*(Fintype.card V:ℝ)^2→(Ns:ℝ)≤η^2*(Fintype.card V:ℝ)^2→
    ∀ (x y:Fin Nr→V) (tr:Fin Nr→Bool),(∀ i,x i∉X)→(∀ i,y i∉X)→
    (∀ i,¬PermutationClose π b (x i) (y i))→
    (∀ i,markedArcPresent tail head ktail khead (tr i) (x i) (y i))→
    Function.Injective (fun i=>if tr i then ({x i,π (y i)}:Finset V) else {x i,y i})→
    (∀ a,((Finset.univ.filter (fun i=>a=x i∨a=y i)).card:ℝ)≤η^2*Fintype.card V)→
    (∀ i,β*Fintype.card V≤((Z.filter (fun v=>H₀ (x i) v∧(if tr i then HK (y i) v else H₀ (y i) v))).card:ℝ))→
    ∀ (z:Fin Ns→V) (u:Fin Ns→U) (ts:Fin Ns→Bool),(∀ i,z i∉X)→(∀ i,u i∉Z)→
    (∀ i,if ts i then HK (z i) (u i) else H₀ (z i) (u i))→
    Function.Injective (fun i=>(z i,u i))→
    (∀ a,((Finset.univ.filter (fun i=>a=z i)).card:ℝ)≤η^2*Fintype.card V)→
    (∀ v,((Finset.univ.filter (fun i=>u i=v)).card:ℝ)≤η^2*Fintype.card V)→
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+4) π b H₀ HK),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) (Zᶜ))=
        Finset.univ.image (fun i=>Sum.inl (if tr i then ({x i,π (y i)}:Finset V) else {x i,y i}))∪
        Finset.univ.image (fun i=>Sum.inr (z i,u i))∧
      (∀ a,((markedPackingRimGraph M).degree a:ℝ)≤24*η*Fintype.card V)∧
      (∀ a,((Finset.univ.filter (markedPackingSpokes M a)).card:ℝ)≤6*η*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (fun a=>markedPackingSpokes M a v)).card:ℝ)≤3*(l+5)*η*Fintype.card V):=by
  intro b hb
  obtain ⟨n₀,hbase⟩:=marked_sparse_inner_domain_edge_packing l hl β hβ η hη hη1 hscale b hb
  refine ⟨n₀,?_⟩
  intro V U E T _ _ _ _ tail head ktail khead H₀ HK π hn hphys X Z hX hstep hjoin Nr Ns hNr hNs
    x y tr hx hy hsep hroot hedge hend hhubs z u ts hz hu hspoke hspinj hsrow hscol
  obtain ⟨R,S,hRI,hSI,hRR,hSS,hRS,hRdeg,hSdeg,hRrow,hSrow,hRcol,hScol⟩:=
    hbase V U E T tail head ktail khead H₀ HK π hn hphys X Z hX hstep hjoin Nr Ns hNr hNs
      x y tr hx hy hsep hroot hedge hend hhubs z u ts hz hu hspoke hspinj hsrow hscol
  let M:=Finset.univ.image R∪Finset.univ.image S
  obtain ⟨hr,hs,hc⟩:=marked_two_families_degree_bounds R S
    (12*η*Fintype.card V) (12*η*Fintype.card V)
    (3*η*Fintype.card V) (3*η*Fintype.card V)
    (2*(l+5)*η*Fintype.card V) ((l+5)*η*Fintype.card V)
    hRdeg hSdeg hRrow hSrow hRcol hScol
  refine ⟨M,marked_two_families_packing R S hRR hSS hRS,
    marked_two_families_inner_intersection R S (Xᶜ) (Zᶜ) _ _ hRI hSI,?_,?_,?_⟩
  · intro a;have h:=hr a;linarith only [h]
  · intro a;have h:=hs a;linarith only [h]
  · intro v;have h:=hc v;linarith only [h]

end Oberwolfach
