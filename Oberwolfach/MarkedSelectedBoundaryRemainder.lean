module

public import Oberwolfach.MarkedSelectedBoundaryCompletion
public import Oberwolfach.MarkedBoundaryCoverage

@[expose] public section

/-! Construct the marked boundary packing and its exact divisible inner
remainder from the actual selected factors and endpoint incidence lists. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T J I:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype T] [Fintype J] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T] [DecidableEq J] [DecidableEq I]
    {tail head:E→V} {ktail khead:T→V} {H₀ HK:V→U→Prop}
    {π:Equiv.Perm V} {b l:ℕ} {c:ℝ}

theorem marked_selected_boundary_divisible_remainder
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
    (hbudget:(Fintype.card (Σ j,Y₀ j⊕Y₁ j)*(l+4):ℕ)/(K:ℝ)+D+(D*(l+4):ℕ)+
      (l+5)*(2*b+1)+2*(δ+4*(K+D:ℕ))<c)
    (hroots:∀ v∉X,∃ j,root j=v) (hhubs:∀ u∉Z,∃ i,hub i=u)
    (hinAll:∀ j a,Sum.elim head khead a=root j→∃ w,incoming j w=a)
    (houtAll:∀ j a,Sum.elim tail ktail a=root j→∃ w,outgoing j w=a)
    (hrowAll:∀ j u,H₀ (root j) u∨HK (root j) u→u∈Y₀ j∪Y₁ j)
    (hcolAll:∀ i v,H₀ v (hub i)∨HK v (hub i)→v∈Y i)
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (hAS:MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) (l+3)):
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+3) π b H₀ HK),
      (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
      (∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤δ+4*(K+D:ℕ))∧
      (∀ v∈X,(Z.filter (markedPackingSpokes M v)).card≤K+D)∧
      (∀ u∈Z,(Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card≤D*(l+4))∧
      (let A':=Finset.univ\M.biUnion markedWheelArcs
       let S':=(Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2))\M.biUnion markedWheelSpokePairs
       MarkedRemainderDivisible tail head ktail khead HK A' S' (l+3)∧
         (∀ a∈A',Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)∧
         (∀ s∈S',s.1∈X∧s.2∈Z)∧
         (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
           (Finset.univ.image (fun a:E⊕T=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
             (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).image Sum.inr)\
             M.biUnion markedWheelPhysicalResources):=by
  obtain ⟨M,hM,hMi,hMo,hMr,hMh,hR,hS,hU,_⟩:=marked_selected_boundary_completion
    X Q hl hb hphys hX root hrootX A₀ A₁ X₀ X₁ Y₀ Y₁ P hcross incoming outgoing
    hinhead hintail houttail houthead hintype houttype hAX hXX hsepA hsepX hY₀ hY₁
    D K hK hdeg Z hYZ hub houtside Y hYX F hFcross hFsep δ hδ hG hbudget
  obtain ⟨hcoverR,hcoverS⟩:=marked_boundary_coverage_from_incidence_lists X Z root hub
    hroots hhubs A₀ A₁ X₀ X₁ Y₀ Y₁ Y (fun j=>(incoming j).toFun) (fun j=>(outgoing j).toFun)
    hinAll houtAll hrowAll hcolAll M hMi hMo hMr hMh
  exact ⟨M,hM,hR,hS,hU,marked_full_host_boundary_remainder hphys hH X Z hAS M hM hcoverR hcoverS⟩

end Oberwolfach
