module

public import Oberwolfach.MarkedCommonHubSwitch
public import Oberwolfach.MarkedHubSwitchResources

@[expose] public section

/-! Actual marked hub-switch resources constructed from the original common
cycle estimates. The output records the support needed for subsequent
packing, without assuming the existence of factors or absorber records. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem marked_common_hub_switch_resources (m:ℕ) (hm:3<m+1)
    (q₀ β blo bhi:ℝ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ qroot:ℕ,∃ t:ℕ,1≤t∧∀ F₀ D:ℝ,0≤F₀→0≤D→∃ N:ℕ,
    ∀ (V U E K:Type) [Fintype V] [DecidableEq V] [DecidableEq U],N≤Fintype.card V→
    ∀ (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (b:ℕ),1≤b→
    ∀ (H₀ HK:V→U→Prop) (F:SimpleGraph V) (u u':U) (A₀ B₀ I ZK ZO:Finset V) (q:ℝ),
    u≠u'→q₀≤q→(∀ v,HK v u→¬H₀ v u)→
    (∀ v∈A₀,HK v u∧HK v u')→(∀ v∈B₀,H₀ v u∧H₀ v u')→
    (∀ v∈ZO,H₀ v u∧H₀ v u')→ZK⊆A₀→Disjoint (ZK∪ZO) I→
    (∀ x∈ZK∪ZO,∀ y∈ZK∪ZO,x≠y→¬PermutationClose π b x y)→
    ZO.card=m*ZK.card→ZK.card≤qroot→(I.card:ℝ)≤ε*Fintype.card V+F₀→
    |(A₀.card:ℝ)-q*Fintype.card V|≤ε*Fintype.card V→
    |(B₀.card:ℝ)-m*q*Fintype.card V|≤ε*Fintype.card V→
    ((B₀∩A₀.image π).card:ℝ)≤ε*Fintype.card V→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→(∀ v,(F.degree v:ℝ)≤D)→
    β*(Fintype.card V:ℝ)^(m+1)≤Fintype.card (ClassMarkedCycle tail head ktail khead m π b A₀ B₀)→
    (∀ j:Bool,∀ v v':V,v≠v'→β*(Fintype.card V:ℝ)^m≤
      Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b
        (fun x (_:Unit)=>x∈B₀) (fun x (_:Unit)=>x∈A₀) j v v' () ()))→
    ∀ w:MarkedCycleTuple tail head ktail khead m π b→ℝ,
    (∀ C,blo/(Fintype.card V:ℝ)^m≤w C∧w C≤bhi/(Fintype.card V:ℝ)^m)→
    (∀ j:Bool,∀ v:V,|1-resourceRootOmittedLoad typedMarkedCycleVertices w
      (fun x=>x∈typedClassSet A₀ B₀) (j,v)|≤ε)→
    ∃ Y:Finset V,∃ P N:Finset (Finset V⊕(V×U)),
      Disjoint Y ((ZK∪ZO)∪I)∧Y.card=(m+1)*t∧
      (∀ x∈Y,∀ y∈Y,¬F.Adj x y)∧
      HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) P∧
      HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) N∧
      (∀ e∈P∪N,MarkedSwitchResource tail head ktail khead π Y (ZK∪ZO) u u' e)∧
      ∀ e:Finset V⊕(V×U),(if e∈P then (1:ℤ) else 0)-(if e∈N then 1 else 0)=
        (if e∈(ZK∪ZO).image (fun v=>Sum.inr (v,u)) then 1 else 0)-
        (if e∈(ZK∪ZO).image (fun v=>Sum.inr (v,u')) then 1 else 0):=by
  obtain ⟨ε,hε,hchoose⟩:=marked_common_hub_switch m hm q₀ β blo bhi hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro qroot
  obtain ⟨t,ht,hchoose⟩:=hchoose qroot
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD
  obtain ⟨N,hchoose⟩:=hchoose F₀ D hF₀ hD
  refine ⟨N,?_⟩
  intro V U E K _ _ _ hn tail head ktail khead π b hb H₀ HK F u u' A₀ B₀ I ZK ZO q hu hq htypes hAK hBO hZO hZA hZI hZsep hZc hz hIc hAc hBc hOc hp hF hbase hpath w hw hroot
  obtain ⟨A,B,Y,M₀,M₁,hZKA,hZOB,hAA,hBB,hdis,hπ,hY,hYI,hYc,hYA,hYB,hYF,hM₀,hM₁,hcover₀,hcover₁,hcap,htrade⟩:=
    hchoose V U E K hn tail head ktail khead π b hb H₀ HK F u u' A₀ B₀ I ZK ZO q hu hq htypes hAK hBO hZO hZA hZI hZsep hZc hz hIc hAc hBc hOc hp hF hbase hpath w hw hroot
  let P:=M₁.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u)∪
    M₀.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u')
  let N':=M₁.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u')∪
    M₀.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u)
  have hs:=marked_two_factor_switch_resources (by omega : 1≤m) A B Y (ZK∪ZO)
    (hYI.mono_right Finset.subset_union_left) u u' M₀ M₁ hcover₀ hcover₁ hcap
  exact ⟨Y,P,N',hYI,hYc,hYF,htrade.1,htrade.2.1,hs,htrade.2.2⟩

end Oberwolfach
