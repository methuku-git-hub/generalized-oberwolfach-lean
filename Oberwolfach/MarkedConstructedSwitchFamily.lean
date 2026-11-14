module

public import Oberwolfach.MarkedConstructedHubSwitch
public import Oberwolfach.MarkedHubSwitchFamilySelection

@[expose] public section

/-! All common-hub switches from the original estimates, with one uniform
size bound and a host-order threshold chosen after the forbidden-set bound,
conflict degree and number of hubs. The construction is sequential and the
original weights and root domains remain fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem marked_constructed_switch_family (m:ℕ) (hm:3<m+1)
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
    ∃ Y:J→Finset V,∃ P N:J→Finset (Finset V⊕(V×U)),
      (∀ i,Disjoint (Y i) W₀∧(Y i).card=(m+1)*t∧(∀ x∈Y i,∀ y∈Y i,¬F.Adj x y)∧
        HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) (P i)∧
        HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) (N i)∧
        (∀ e∈P i∪N i,MarkedSwitchResource tail head ktail khead π (Y i) (ZK i∪ZO i) (u i) (u' i) e)∧
        ∀ e,(if e∈P i then (1:ℤ) else 0)-(if e∈N i then 1 else 0)=
          (if e∈(ZK i∪ZO i).image (fun v=>Sum.inr (v,u i)) then 1 else 0)-
          (if e∈(ZK i∪ZO i).image (fun v=>Sum.inr (v,u' i)) then 1 else 0))∧
      (∀ i j,i≠j→Disjoint (Y i∪(ZK i∪ZO i)) (Y j∪(ZK j∪ZO j))∧
        (∀ x∈Y i,∀ y∈Y j,¬F.Adj x y)∧Disjoint (P i∪N i) (P j∪N j)):=by
  obtain ⟨ε,hε,hchoose⟩:=marked_common_hub_switch_resources m hm q₀ β blo bhi hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro qroot
  obtain ⟨t,ht,hchoose⟩:=hchoose qroot
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD k
  let d:ℕ:=(m+1)*t
  let Fstar:ℝ:=F₀+k*d*(D+1)
  have hFstar:0≤Fstar:=by dsimp [Fstar];positivity
  obtain ⟨N,hchoose⟩:=hchoose Fstar D hFstar hD
  refine ⟨N,?_⟩
  intro V U E K J _ _ _ _ _ hn hk tail head ktail khead π b hb H₀ HK F u u' A₀ B₀ ZK ZO W₀ q hu hq htypes hAK hBO hZO hZA hZW hZZ hZsep hZc hz hWc hAc hBc hOc hp hF hbase hpath w hw hroot
  apply marked_hub_switch_family_selection hp markedWheelPhysicalResources
    (fun i=>ZK i∪ZO i) u u' W₀ hZW hZZ d F D hD hF
  intro i B hB hZB
  have hB':(B.card:ℝ)≤ε*Fintype.card V+Fstar:=by
    have hk':(Fintype.card J:ℝ)≤k:=by exact_mod_cast hk
    have hm':(Fintype.card J:ℝ)*d*(D+1)≤(k:ℝ)*d*(D+1):=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk' (by positivity)) (by linarith)
    dsimp only [Fstar]
    linarith
  exact hchoose V U E K hn tail head ktail khead π b hb H₀ HK F (u i) (u' i)
    (A₀ i) (B₀ i) B (ZK i) (ZO i) (q i) (hu i) (hq i) (fun v=>htypes v (u i))
    (hAK i) (hBO i) (hZO i) (hZA i) hZB (hZsep i) (hZc i) (hz i) hB'
    (hAc i) (hBc i) (hOc i) hp hF (hbase i) (hpath i) (w i) (hw i) (hroot i)

end Oberwolfach
