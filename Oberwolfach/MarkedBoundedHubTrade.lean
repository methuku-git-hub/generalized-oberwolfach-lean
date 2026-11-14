module

public import Oberwolfach.MarkedBoundedTwoFactors
public import Oberwolfach.MarkedClassFactorTrade

@[expose] public section

/-! A bounded hub trade constructed from the original marked cycle weights
and absorber counts. The two factors are produced by the proved theorem;
they are not inputs to this construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 13000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem marked_bounded_hub_trade (m:ℕ) (hm:2≤m)
    (S:Tpl→VertexAbsorberTemplate (m+1)) (α b₀ B₀:ℝ) (hα:0<α) (hb₀:0<b₀) (hB₀:0<B₀):
    ∃ η:ℝ,0<η ∧ ∀ q:ℕ,∃ t:ℕ,1≤t ∧ ∀ F₀ D:ℝ,0≤F₀→0≤D→
      ∃ k₀:ℝ,1<k₀ ∧ ∀ k:ℝ,k₀≤k→
      ∀ (V U E K:Type) [Fintype V] [DecidableEq V] [DecidableEq U],
      ∀ (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (b:ℕ)
        (H₀ HK:V→U→Prop) (F:SimpleGraph V) (A B:Finset V) (u u':U),u≠u'→
      Disjoint A B→(A.card:ℝ)=k→(B.card:ℝ)=m*k→
      (∀ v∈A,HK v u∧HK v u')→(∀ v∈B,H₀ v u∧H₀ v u')→
      Function.Injective (markedPhysicalEdge tail head ktail khead π)→(∀ v,(F.degree v:ℝ)≤D)→
      ∀ w:ClassMarkedCycle tail head ktail khead m π b A B→ℝ,
      (∀ C,b₀/k^m≤w C ∧ w C≤B₀/k^m)→
      (∀ v∈A∪B,|1-hypergraphWeightedDegree classMarkedCycleVertices w v|≤η)→
      (∀ X:Finset V,X⊆A∪B→(X∩A).card=1→(X∩B).card=m→α*k^((m+1)*(m+1))≤
        Fintype.card (LabelledAbsorberFamily (classMarkedCycleVertices (tail:=tail) (head:=head)
          (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (A:=A) (B:=B)) S X))→
      ∀ (I Z:Finset V) (z:ℕ),(I.card:ℝ)≤F₀→Z⊆A∪B→(Z∩A).card=z→(Z∩B).card=m*z→z≤q→
      ∃ Y:Finset V,∃ M₀ M₁:Finset (ClassMarkedCycle tail head ktail khead m π b A B),
        Y⊆A∪B ∧ Disjoint Y (Z∪I) ∧ Y.card=(m+1)*t ∧
        (Y∩A).card=t ∧ (Y∩B).card=m*t ∧ (∀ x∈Y,∀ y∈Y,¬F.Adj x y) ∧
        (∀ C∈M₀,∀ C'∈M₀,C≠C'→Disjoint (classMarkedCycleVertices C) (classMarkedCycleVertices C')) ∧
        (∀ C∈M₁,∀ C'∈M₁,C≠C'→Disjoint (classMarkedCycleVertices C) (classMarkedCycleVertices C')) ∧
        M₀.biUnion classMarkedCycleVertices=Y ∧ M₁.biUnion classMarkedCycleVertices=Y∪Z ∧
        (∀ C∈M₁,(classMarkedCycleVertices C∩Z).card≤1) ∧
        let P:=M₁.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u)∪
          M₀.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u')
        let N:=M₁.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u')∪
          M₀.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u)
        HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) P∧
        HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) N∧
        ∀ e:Finset V⊕(V×U),(if e∈P then (1:ℤ) else 0)-(if e∈N then 1 else 0)=
          (if e∈Z.image (fun v=>Sum.inr (v,u)) then 1 else 0)-
          (if e∈Z.image (fun v=>Sum.inr (v,u')) then 1 else 0):=by
  obtain ⟨η,hη,hbase⟩:=marked_bounded_two_factors m hm S α b₀ B₀ hα hb₀ hB₀
  refine ⟨η,hη,?_⟩
  intro q
  obtain ⟨t,ht,hbase⟩:=hbase q
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD
  obtain ⟨k₀,hk₀,hbase⟩:=hbase F₀ D hF₀ hD
  refine ⟨k₀,hk₀,?_⟩
  intro k hk V U E K _ _ _ tail head ktail khead π b H₀ HK F A B u u' hu hAB hAc hBc hK hO hp hF w hw herr habs I Z z hI hZT hZA hZB hz
  obtain ⟨Y,M₀,M₁,hYAB,hYI,hYA,hYB,hYF,h₀,h₁,hdis,hcap⟩:=hbase k hk V E K tail head ktail khead π b F A B hAB hAc hBc hp hF w hw herr habs I Z z hI hZT hZA hZB hz
  have hYcard:Y.card=(m+1)*t:=by
    have he:Y=(Y∩A)∪(Y∩B):=by
      ext v
      simp only [Finset.mem_union,Finset.mem_inter]
      have h:v∈Y→v∈A∨v∈B:=fun hv=>Finset.mem_union.mp (hYAB hv)
      tauto
    have hd:Disjoint (Y∩A) (Y∩B):=hAB.mono Finset.inter_subset_right Finset.inter_subset_right
    have hh:=congrArg Finset.card he
    rw [Finset.card_union_of_disjoint hd,hYA,hYB] at hh
    rw [Nat.add_mul,Nat.one_mul]
    omega
  refine ⟨Y,M₀,M₁,hYAB,hYI,hYcard,hYA,hYB,hYF,h₀.1,h₁.1,h₀.2,h₁.2,hcap,?_⟩
  exact class_marked_factor_trade H₀ HK hp A B Y Z (hYI.mono_right Finset.subset_union_left)
    u u' hu hK hO M₀ M₁ h₀ h₁ hdis

end Oberwolfach
