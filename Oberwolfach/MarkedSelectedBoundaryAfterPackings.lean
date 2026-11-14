module

public import Oberwolfach.MarkedSelectedBoundaryAfterPhysicalDeletion
public import Oberwolfach.MarkedBoundaryAfterPacking
public import Oberwolfach.MarkedBoundaryPhysicalDeletion
public import Oberwolfach.MarkedHubFactorPhysicalRestriction
public import Oberwolfach.MarkedEndpointPhysicalRestriction
public import Oberwolfach.MarkedPackingPhysicalAvoidance
public import Oberwolfach.MarkedRootArcRestriction

@[expose] public section

/-! Complete the selected boundary in the original host after an earlier packing outside the inner pair
and a subsequent covering of small maximum degree. The incoming and outgoing arcs, root spokes, selected
factors and endpoint assignments all retain their original identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T J I:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype T] [Fintype J] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T] [DecidableEq J] [DecidableEq I]
    {tail head:E→V} {ktail khead:T→V} {H₀ HK:V→U→Prop}
    {π:Equiv.Perm V} {b l:ℕ} {c:ℝ}

theorem marked_selected_boundary_after_packings
    (X:Finset V) (Q:MarkedBoundaryExtensionCounts tail head ktail khead H₀ HK X c)
    (hl:2≤l) (hb:1≤b) (hphys:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hX:∀ x,π x∈X↔x∈X) (root:J↪V) (hrootX:∀ j,root j∉X)
    (A₀ A₁ X₀ X₁:J→Finset V) (Y₀ Y₁:J→Finset U)
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (hcross:∀ j k,j≠k→Disjoint (P j).graph (P k).graph)
    (incoming:∀ j,(A₀ j⊕A₁ j)↪E⊕T) (outgoing:∀ j,(X₀ j⊕X₁ j)↪E⊕T)
    (hinhead:∀ j a,Sum.elim head khead (incoming j a)=root j)
    (hintail:∀ j a,Sum.elim tail ktail (incoming j a)=taggedSubsetValue (A₀ j) (A₁ j) a)
    (houttail:∀ j a,Sum.elim tail ktail (outgoing j a)=root j)
    (houthead:∀ j a,Sum.elim head khead (outgoing j a)=taggedSubsetValue (X₀ j) (X₁ j) a)
    (hintype:∀ j a,(incoming j a).isRight=a.isRight)
    (houttype:∀ j a,(outgoing j a).isRight=a.isRight)
    (hAX:∀ j,A₀ j∪A₁ j⊆X) (hXX:∀ j,X₀ j∪X₁ j⊆X)
    (hsepA:∀ j a,a∈A₀ j∪A₁ j→¬PermutationClose π b a (root j))
    (hsepX:∀ j a,a∈X₀ j∪X₁ j→¬PermutationClose π b a (root j))
    (hY₀:∀ j u,u∈Y₀ j→H₀ (root j) u) (hY₁:∀ j u,u∈Y₁ j→HK (root j) u)
    (D K:ℕ) (hK:0<K) (hdeg:∀ w,(⨆ j,(P j).graph).degree w≤D)
    (Z:Finset U) (hYZ:∀ j,Y₀ j∪Y₁ j⊆Z)
    (hub:I↪U) (houtside:∀ j,hub j∉Z) (Y:I→Finset V) (hYX:∀ j,Y j⊆X)
    (F:∀ j,MarkedHubFactorOn tail head ktail khead (l+3) π b H₀ HK (hub j) (Y j))
    (hFcross:∀ j k,j≠k→Disjoint (F j).rim (F k).rim)
    (hFsep:∀ j v z,H₀ v (hub j)→HK z (hub j)→v≠π z)
    (δ:ℝ) (hδ:0≤δ) (hG:∀ v,((⨆ j,(F j).rim).degree v:ℝ)≤δ)
    (M₀ M₁:Finset (MarkedWheel tail head ktail khead (l+3) π b H₀ HK))
    (hM₀:∀ W∈M₀,∀ W'∈M₀,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))
    (hM₁:∀ W∈M₁,∀ W'∈M₁,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))
    (hM₀₁:Disjoint (M₀.biUnion markedWheelPhysicalResources) (M₁.biUnion markedWheelPhysicalResources))
    (hM₀inner:∀ e∈M₀.biUnion markedWheelPhysicalResources,¬markedInnerResource X Z e)
    (hinM₀:∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming j a))∉M₀.biUnion markedWheelPhysicalResources)
    (houtM₀:∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing j a))∉M₀.biUnion markedWheelPhysicalResources)
    (hrootM₀:∀ j u,u∈Y₀ j∪Y₁ j→Sum.inr (root j,u)∉M₀.biUnion markedWheelPhysicalResources)
    (hfactorM₀:∀ j x,x∈Y j→Sum.inr (x,hub j)∉M₀.biUnion markedWheelPhysicalResources)
    (D₀:SimpleGraph (V⊕U)) (hD₀eq:D₀=ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)) (δ₀:ℝ) (hδ₀:0≤δ₀) (hD₀:∀ z,(D₀.degree z:ℝ)≤δ₀)
    (hPD₀:∀ j,Disjoint (P j).graph D₀) (hFD₀:∀ i,Disjoint (F i).graph D₀)
    (hrootSpokeD₀:∀ j u,u∈Y₀ j∪Y₁ j→¬D₀.Adj (Sum.inl (root j)) (Sum.inr u))
    (hfactorSpokeD₀:∀ i v,v∈Y i→¬D₀.Adj (Sum.inl v) (Sum.inr (hub i)))
    (hinD₀:∀ j a,Sum.elim
      (fun e=>¬D₀.Adj (Sum.inl (tail e)) (Sum.inl (head e)))
      (fun e=>¬D₀.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))) (incoming j a))
    (houtD₀:∀ j a,Sum.elim
      (fun e=>¬D₀.Adj (Sum.inl (tail e)) (Sum.inl (head e)))
      (fun e=>¬D₀.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))) (outgoing j a))
    (hbudget:(Fintype.card (Σ j,Y₀ j⊕Y₁ j)*(l+4):ℕ)/(K:ℝ)+D+(D*(l+4):ℕ)+
      (l+5)*(2*b+1)+2*(δ+4*(K+D:ℕ))<c-3*δ₀)
    (hroots:∀ v∉X,∃ j,root j=v) (hhubs:∀ u∉Z,∃ i,hub i=u)
    (hinAll:∀ j a,Sum.elim head khead a=root j→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉(M₀∪M₁).biUnion markedWheelPhysicalResources→∃ w,incoming j w=a)
    (houtAll:∀ j a,Sum.elim tail ktail a=root j→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉(M₀∪M₁).biUnion markedWheelPhysicalResources→∃ w,outgoing j w=a)
    (hrowAll:∀ j u,H₀ (root j) u∨HK (root j) u→
      Sum.inr (root j,u)∉(M₀∪M₁).biUnion markedWheelPhysicalResources→u∈Y₀ j∪Y₁ j)
    (hcolAll:∀ i v,H₀ v (hub i)∨HK v (hub i)→
      Sum.inr (v,hub i)∉(M₀∪M₁).biUnion markedWheelPhysicalResources→v∈Y i)
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (hdiv:MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) (l+3)):
    ∃ N:Finset (MarkedWheel tail head ktail khead (l+3) π b H₀ HK),
      Disjoint ((M₀∪M₁).biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources)∧
      (∀ v,((spanningRestriction (markedPackingRimGraph N) X).degree v:ℝ)≤δ+4*(K+D:ℕ))∧
      (∀ v∈X,(Z.filter (markedPackingSpokes N v)).card≤K+D)∧
      (∀ u∈Z,(Finset.univ.filter (fun v=>markedPackingSpokes N v u)).card≤D*(l+4))∧
      (let M:=M₀∪M₁∪N
       (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
       (let A':=Finset.univ\M.biUnion markedWheelArcs
        let S':=(Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2))\M.biUnion markedWheelSpokePairs
        MarkedRemainderDivisible tail head ktail khead HK A' S' (l+3)∧
          (∀ a∈A',Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)∧
          (∀ s∈S',s.1∈X∧s.2∈Z)∧
          (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
            (Finset.univ.image (fun a:E⊕T=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
              (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).image Sum.inr)\
              M.biUnion markedWheelPhysicalResources)):=by
  obtain ⟨N,hN,hi,ho,hr,hf,hrim,hrow,hcol,hD,havoid⟩:=marked_selected_boundary_after_physical_deletion
    X Q hl hb hphys hX root hrootX A₀ A₁ X₀ X₁ Y₀ Y₁ P hcross incoming outgoing
    hinhead hintail houttail houthead hintype houttype hAX hXX hsepA hsepX hY₀ hY₁
    D K hK hdeg Z hYZ hub houtside Y hYX F hFcross hFsep δ hδ hG
    D₀ δ₀ hδ₀ hD₀ hPD₀ hFD₀ hrootSpokeD₀ hfactorSpokeD₀ hinD₀ houtD₀ hbudget
  have hN₀:=havoid (M₀.biUnion markedWheelPhysicalResources) hM₀inner hinM₀ houtM₀ hrootM₀ hfactorM₀
  have hN₁:Disjoint (N.biUnion markedWheelPhysicalResources) (M₁.biUnion markedWheelPhysicalResources):=by
    apply marked_packings_disjoint_of_physical_graphs (by omega:1≤l+3) hb N M₁
    rw [←hD₀eq]
    exact hD
  have hMN:Disjoint ((M₀∪M₁).biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources):=by
    rw [Finset.union_biUnion]
    exact disjoint_sup_left.mpr ⟨hN₀.symm,hN₁.symm⟩
  have hM:∀ W∈M₀∪M₁,∀ W'∈M₀∪M₁,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'):=by
    intro W hW W' hW' hne
    rcases Finset.mem_union.mp hW with hW|hW <;> rcases Finset.mem_union.mp hW' with hW'|hW'
    · exact hM₀ W hW W' hW' hne
    · exact hM₀₁.mono (resource_subset_union _ _ W hW) (resource_subset_union _ _ W' hW')
    · exact hM₀₁.symm.mono (resource_subset_union _ _ W hW) (resource_subset_union _ _ W' hW')
    · exact hM₁ W hW W' hW' hne
  refine ⟨N,hMN,hrim,hrow,hcol,?_⟩
  apply marked_boundary_remainder_after_packing hphys hH X Z (M₀∪M₁) N hM hN hMN root hub hroots hhubs
  · intro j a ha hrem
    rcases ha with ht|hh
    · obtain ⟨w,rfl⟩:=houtAll j a ht hrem
      exact ho j w
    · obtain ⟨w,rfl⟩:=hinAll j a hh hrem
      exact hi j w
  · intro j u hu hrem
    exact hr j u (hrowAll j u hu hrem)
  · intro j x hx hrem
    exact hf j x (hcolAll j x hx hrem)
  · exact hdiv

end Oberwolfach
