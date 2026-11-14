module

public import Oberwolfach.CommonClassBalancedProfiles
public import Oberwolfach.MarkedBoundedHubTrade
public import Oberwolfach.MarkedClassScaleTransfer
public import Oberwolfach.CommonClassRootCompatibility

@[expose] public section

/-! Bounded two-hub switch from the supplied original common-cycle profile.
Balanced classes, paired absorber records and both factors are constructed.
The original permutation, cycle coefficients and omitted-root tests remain
unchanged. The size bound is chosen before the forbidden-set bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem marked_common_hub_switch (m:ℕ) (hm:3<m+1)
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
    ∃ A B Y:Finset V,∃ M₀ M₁:Finset (ClassMarkedCycle tail head ktail khead m π b A B),
      ZK⊆A∧ZO⊆B∧A⊆A₀∧B⊆B₀∪ZO∧Disjoint A B∧Disjoint B (A.image π)∧
      Y⊆A∪B∧Disjoint Y ((ZK∪ZO)∪I)∧Y.card=(m+1)*t∧
      (Y∩A).card=t∧(Y∩B).card=m*t∧(∀ x∈Y,∀ y∈Y,¬F.Adj x y)∧
      (∀ C∈M₀,∀ C'∈M₀,C≠C'→Disjoint (classMarkedCycleVertices C) (classMarkedCycleVertices C'))∧
      (∀ C∈M₁,∀ C'∈M₁,C≠C'→Disjoint (classMarkedCycleVertices C) (classMarkedCycleVertices C'))∧
      M₀.biUnion classMarkedCycleVertices=Y∧M₁.biUnion classMarkedCycleVertices=Y∪(ZK∪ZO)∧
      (∀ C∈M₁,(classMarkedCycleVertices C∩(ZK∪ZO)).card≤1)∧
      let P:=M₁.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u)∪
        M₀.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u')
      let N:=M₁.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u')∪
        M₀.biUnion (fun C=>markedCycleResourcesAtHub (classMarkedCycleAsMarked C) u)
      HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) P∧
      HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) N∧
      ∀ e:Finset V⊕(V×U),(if e∈P then (1:ℤ) else 0)-(if e∈N then 1 else 0)=
        (if e∈(ZK∪ZO).image (fun v=>Sum.inr (v,u)) then 1 else 0)-
        (if e∈(ZK∪ZO).image (fun v=>Sum.inr (v,u')) then 1 else 0):=by
  let a:=q₀/2
  have ha:0<a:=by dsimp [a];positivity
  let α:ℝ:=(β/4)^(m+2)
  have hα:0<α:=by dsimp [α];positivity
  let blo':=blo*a^m
  have hblo':0<blo':=by dsimp [blo'];positivity
  obtain ⟨η,hη,hfactor⟩:=marked_bounded_hub_trade m (by omega)
    (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) α blo' bhi hα hblo' hbhi
  obtain ⟨ε₀,hε₀,hbalance⟩:=common_class_balanced_profiles m hm q₀ β blo bhi η hq₀ hβ hblo hbhi hη
  let ε:ℝ:=ε₀/2
  have hε:0<ε:=by dsimp [ε];positivity
  have hεle:ε≤ε₀:=by dsimp [ε];linarith
  refine ⟨ε,hε,?_⟩
  intro qroot
  obtain ⟨t,ht,hfactor⟩:=hfactor qroot
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD
  obtain ⟨k₀,hk₀,hfactor⟩:=hfactor 0 D (by positivity) hD
  obtain ⟨Nb,hNb,hbalance⟩:=hbalance (m*qroot) (by positivity)
  obtain ⟨Nt,hNt⟩:=exists_nat_gt (max (k₀/a) (F₀/ε))
  refine ⟨max Nb Nt,?_⟩
  intro V U E K _ _ _ hn tail head ktail khead π b hb H₀ HK F u u' A₀ B₀ I ZK ZO q hu hq htypes hAK hBO hZO hZA hZI hZsep hZc hz hIc hAc hBc hOc hp hF hbase hpath w hw hroot
  have hnb:Nb≤Fintype.card V:=(le_max_left _ _).trans hn
  have hnt:(Nt:ℝ)≤Fintype.card V:=by exact_mod_cast (le_max_right Nb Nt).trans hn
  have hn1:1≤Fintype.card V:=hNb.trans hnb
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by omega)
  have hkbig:k₀≤a*Fintype.card V:=by
    have hh:k₀/a≤Fintype.card V:=(le_max_left _ _).trans (hNt.le.trans hnt)
    nlinarith only [(div_le_iff₀ ha).mp hh]
  have hIε:(I.card:ℝ)≤ε₀*Fintype.card V:=by
    have hh:F₀/ε≤Fintype.card V:=(le_max_right _ _).trans (hNt.le.trans hnt)
    have hh':F₀≤ε*Fintype.card V:=by nlinarith only [(div_le_iff₀ hε).mp hh]
    dsimp only [ε] at hIc hh'
    linarith
  have hAB:=common_class_spoke_disjoint H₀ HK u htypes A₀ B₀ ZO
    (fun v hv=>(hAK v hv).1) (fun v hv=>(hBO v hv).1) (fun v hv=>(hZO v hv).1)
  have hZdis:Disjoint ZK ZO:=hAB.mono hZA Finset.subset_union_right
  have hZπ:=separated_root_successor_disjoint π b hb ZK ZO hZdis hZsep
  have hZOc:(ZO.card:ℝ)≤(m:ℝ)*qroot:=by rw [hZc,Nat.cast_mul];exact_mod_cast Nat.mul_le_mul_left m hz
  obtain ⟨A,B,hZKA,hZOB,hAA,hBB,hdis,hI,hπ,hcard,hsize,hweights,habs⟩:=
    hbalance V E K hnb tail head ktail khead π b A₀ B₀ I ZK ZO q hq hAB hZA hZI hZπ hZc
      (hAc.trans (mul_le_mul_of_nonneg_right hεle hn0.le))
      (hBc.trans (mul_le_mul_of_nonneg_right hεle hn0.le)) hIε
      (hOc.trans (mul_le_mul_of_nonneg_right hεle hn0.le)) hZOc hbase hpath w hw
      (fun j v=>(hroot j v).trans hεle)
  let k:ℝ:=A.card
  have hk:k₀≤k:=hkbig.trans hsize
  have hk0:0≤k:=by dsimp [k];positivity
  have hkn:k≤(Fintype.card V:ℝ):=by dsimp [k];exact_mod_cast Finset.card_le_univ A
  have hBc':(B.card:ℝ)=m*k:=by rw [hcard,Nat.cast_mul]
  have hK':∀ v∈A,HK v u∧HK v u':=fun v hv=>hAK v (hAA hv)
  have hO':∀ v∈B,H₀ v u∧H₀ v u':=by
    intro v hv
    rcases Finset.mem_union.mp (hBB hv) with hv|hv
    · exact hBO v hv
    · exact hZO v hv
  have hw':∀ C:ClassMarkedCycle tail head ktail khead m π b A B,
      blo'/k^m≤w (classMarkedCycleAsMarked C)∧w (classMarkedCycleAsMarked C)≤bhi/k^m:=by
    intro C
    exact marked_class_weight_rescale m a (Fintype.card V) k blo bhi _ ha hn0 hsize hkn hblo.le hbhi.le
      (hw (classMarkedCycleAsMarked C))
  have habs':∀ X:Finset V,X⊆A∪B→(X∩A).card=1→(X∩B).card=m→α*k^((m+1)*(m+1))≤
      Fintype.card (LabelledAbsorberFamily (classMarkedCycleVertices (tail:=tail) (head:=head)
        (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (A:=A) (B:=B))
        (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) X):=by
    intro X hX hXA hXB
    exact marked_class_count_rescale _ α (Fintype.card V) k _ hα.le hk0 hkn (habs X hX hXA hXB)
  have hZT:ZK∪ZO⊆A∪B:=Finset.union_subset_union hZKA hZOB
  have hZKA':((ZK∪ZO)∩A).card=ZK.card:=by
    congr 1
    ext v
    simp only [Finset.mem_inter,Finset.mem_union]
    constructor
    · rintro ⟨hv,ha⟩
      exact hv.resolve_right (fun hz=>Finset.disjoint_left.mp hdis ha (hZOB hz))
    · intro hv;exact ⟨Or.inl hv,hZKA hv⟩
  have hZOB':((ZK∪ZO)∩B).card=m*ZK.card:=by
    rw [←hZc]
    congr 1
    ext v
    simp only [Finset.mem_inter,Finset.mem_union]
    constructor
    · rintro ⟨hv,hb⟩
      exact hv.resolve_left (fun hz=>Finset.disjoint_left.mp hdis (hZKA hz) hb)
    · intro hv;exact ⟨Or.inr hv,hZOB hv⟩
  obtain ⟨Y,M₀,M₁,hY,hYI,hYc,hYA,hYB,hYF,hM₀,hM₁,hcover₀,hcover₁,hcap,htrade⟩:=
    hfactor k hk V U E K tail head ktail khead π b H₀ HK F A B u u' hu hdis rfl hBc' hK' hO' hp hF
      (fun C=>w (classMarkedCycleAsMarked C)) hw' hweights habs' ∅ (ZK∪ZO) ZK.card (by simp) hZT hZKA' hZOB' hz
  have hYI':Disjoint Y ((ZK∪ZO)∪I):=by
    rw [Finset.disjoint_union_right]
    exact ⟨hYI.mono_right Finset.subset_union_left,hI.mono_left hY⟩
  exact ⟨A,B,Y,M₀,M₁,hZKA,hZOB,hAA,hBB,hdis,hπ,hY,hYI',hYc,hYA,hYB,hYF,hM₀,hM₁,hcover₀,hcover₁,hcap,htrade⟩

end Oberwolfach
