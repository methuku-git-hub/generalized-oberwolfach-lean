module

public import Oberwolfach.MarkedConstructedSwitchFamily
public import Oberwolfach.MarkedTransformerSwitchAssembly

@[expose] public section

/-! Complete a packed marked wheel construction from its original common
cycle estimates. Both factors for every hub switch are constructed; no
factor or absorber-existence hypothesis is supplied to this theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
open scoped BigOperators
attribute [local instance] Classical.propDecidable

 theorem marked_profile_transformer_completion (m:ℕ) (hm:3<m+1)
    (q₀ β blo bhi:ℝ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ qroot:ℕ,∃ t:ℕ,1≤t∧∀ F₀ D:ℝ,0≤F₀→0≤D→∀ k:ℕ,∃ N:ℕ,
    ∀ (V U E K J:Type) [Fintype V] [DecidableEq V] [DecidableEq U] [Fintype J] [DecidableEq J],
    N≤Fintype.card V→Fintype.card J≤k→
    ∀ (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (b:ℕ),1≤b→
    ∀ (H₀ HK:V→U→Prop) (F:SimpleGraph V) (u u':J→U)
      (A₀ B₀ ZK ZO:J→Finset V) (W₀:Finset V) (q:J→ℝ),
    (∀ i,u i≠u' i)→(∀ i,q₀≤q i)→(∀ v u,HK v u→¬H₀ v u)→
    (∀ i,∀ v∈A₀ i,HK v (u i)∧HK v (u' i))→
    (∀ i,∀ v∈B₀ i,H₀ v (u i)∧H₀ v (u' i))→
    (∀ i,∀ v∈ZO i,H₀ v (u i)∧H₀ v (u' i))→
    (∀ i,ZK i⊆A₀ i)→(∀ i,ZK i∪ZO i⊆W₀)→
    (∀ i j,i≠j→Disjoint (ZK i∪ZO i) (ZK j∪ZO j))→
    (∀ i,∀ x∈ZK i∪ZO i,∀ y∈ZK i∪ZO i,x≠y→¬PermutationClose π b x y)→
    (∀ i,(ZO i).card=m*(ZK i).card)→(∀ i,(ZK i).card≤qroot)→(W₀.card:ℝ)≤ε*Fintype.card V+F₀→
    (∀ i,|((A₀ i).card:ℝ)-q i*Fintype.card V|≤ε*Fintype.card V)→
    (∀ i,|((B₀ i).card:ℝ)-m*q i*Fintype.card V|≤ε*Fintype.card V)→
    (∀ i,((B₀ i∩(A₀ i).image π).card:ℝ)≤ε*Fintype.card V)→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→(∀ v,(F.degree v:ℝ)≤D)→
    (∀ i,β*(Fintype.card V:ℝ)^(m+1)≤Fintype.card (ClassMarkedCycle tail head ktail khead m π b (A₀ i) (B₀ i)))→
    (∀ i,∀ j:Bool,∀ v v':V,v≠v'→β*(Fintype.card V:ℝ)^m≤
      Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b
        (fun x (_:Unit)=>x∈B₀ i) (fun x (_:Unit)=>x∈A₀ i) j v v' () ()))→
    ∀ w:J→MarkedCycleTuple tail head ktail khead m π b→ℝ,
    (∀ i C,blo/(Fintype.card V:ℝ)^m≤w i C∧w i C≤bhi/(Fintype.card V:ℝ)^m)→
    (∀ i,∀ j:Bool,∀ v:V,|1-resourceRootOmittedLoad typedMarkedCycleVertices (w i)
      (fun x=>x∈typedClassSet (A₀ i) (B₀ i)) (j,v)|≤ε)→
    ∀ P₀ N₀ L L':Finset (Finset V⊕(V×U)),Disjoint L L'→
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) P₀→
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) N₀→
    (∀ e∈P₀,MarkedResourceSupported tail head ktail khead π W₀ e)→
    (∀ e∈N₀,MarkedResourceSupported tail head ktail khead π W₀ e)→
    (∀ i,∀ v∈ZK i∪ZO i,(Sum.inr (v,u' i):Finset V⊕(V×U))∉P₀∧
      (Sum.inr (v,u i):Finset V⊕(V×U))∉N₀)→
    (∀ e,(if e∈P₀ then (1:ℤ) else 0)-(if e∈N₀ then 1 else 0)=
      (if e∈L then 1 else 0)-(if e∈L' then 1 else 0)+
        ∑ i,((if e∈(ZK i∪ZO i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
          (if e∈(ZK i∪ZO i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0)))→
    ∃ Yall:Finset V,∃ T:Finset (Finset V⊕(V×U)),
      Disjoint Yall W₀∧Yall.card≤k*((m+1)*t)∧
      (∀ x∈Yall,∀ y∈Yall,¬F.Adj x y)∧
      IsResourceTransformer (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) L L' T∧
      (∀ e∈T,MarkedResourceSupported tail head ktail khead π (W₀∪Yall) e)∧
      ∀ e∈T,e∉P₀→∃ i,MarkedSwitchResource tail head ktail khead π Yall (ZK i∪ZO i) (u i) (u' i) e:=by
  obtain ⟨ε,hε,hchoose⟩:=marked_constructed_switch_family m hm q₀ β blo bhi hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro qroot
  obtain ⟨t,ht,hchoose⟩:=hchoose qroot
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD k
  obtain ⟨N,hchoose⟩:=hchoose F₀ D hF₀ hD k
  refine ⟨N,?_⟩
  intro V U E K J _ _ _ _ _ hn hk tail head ktail khead π b hb H₀ HK F u u' A₀ B₀ ZK ZO W₀ q hu hq htypes hAK hBO hZO hZA hZW hZZ hZsep hZc hz hWc hAc hBc hOc hp hF hbase hpath w hw hroot P₀ N₀ L L' hLL hP₀ hN₀ hPW hNW hsp h₀
  obtain ⟨Y,P,N',hY,hdis⟩:=hchoose V U E K J hn hk tail head ktail khead π b hb H₀ HK F u u'
    A₀ B₀ ZK ZO W₀ q hu hq htypes hAK hBO hZO hZA hZW hZZ hZsep hZc hz hWc hAc hBc hOc hp hF hbase hpath w hw hroot
  obtain ⟨Yall,T,hYa,hYd,hYc,hT,hTs,hTW,hnew⟩:=marked_transformer_switch_assembly hp markedWheelPhysicalResources
    Y (fun i=>ZK i∪ZO i) u u' W₀ ((m+1)*t) k hk (fun i=>⟨(hY i).1,(hY i).2.1⟩) hZW hu P N'
    (fun i=>(hY i).2.2.2.1) (fun i=>(hY i).2.2.2.2.1) (fun i j hij=>(hdis i j hij).2.2)
    (fun i=>(hY i).2.2.2.2.2.1) (fun i=>(hY i).2.2.2.2.2.2) P₀ N₀ L L' hLL hP₀ hN₀ hPW hNW hsp h₀
  have hYF:∀ x∈Yall,∀ y∈Yall,¬F.Adj x y:=by
    intro x hx y hy
    rw [hYa] at hx hy
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hy
    by_cases hij:i=j
    · subst j;exact (hY i).2.2.1 x hi y hj
    · exact (hdis i j hij).2.1 x hi y hj
  refine ⟨Yall,T,hYd,hYc,hYF,hT,hTW,?_⟩
  intro e he hn
  obtain ⟨i,hi,hs⟩:=hnew e he hn
  have hYi:Y i⊆Yall:=by rw [hYa];exact fun v hv=>Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩
  refine ⟨i,?_⟩
  cases e with
  | inl e=>
    obtain ⟨a,ha,ht,hh,hy⟩:=hs
    exact ⟨a,ha,(Finset.union_subset_union hYi (Finset.Subset.refl _)) ht,
      (Finset.union_subset_union hYi (Finset.Subset.refl _)) hh,hy.imp (fun h=>hYi h) (fun h=>hYi h)⟩
  | inr vu=>
    exact ⟨(Finset.union_subset_union hYi (Finset.Subset.refl _)) hs.1,hs.2⟩

end Oberwolfach
