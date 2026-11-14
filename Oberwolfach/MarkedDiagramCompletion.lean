module

public import Oberwolfach.MarkedDiagramHubProfiles
public import Oberwolfach.MarkedInitialDiagramOldResources
public import Oberwolfach.MarkedDiagramHubSupport
public import Oberwolfach.MarkedProfileTransformerCompletion

@[expose] public section

/-! Complete the actual initial diagram. All initial wheels, their packing,
signed identity, switch roots and support are derived from the diagram.
Only original common-cycle estimates are supplied for the hub switches. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_diagram_completion (l:ℕ)
    (q₀ β blo bhi:ℝ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ s:ℕ,∃ t:ℕ,1≤t∧∀ F₀ dF:ℝ,0≤F₀→0≤dF→∃ N:ℕ,
    ∀ (V U E K A S:Type) [Fintype V] [Fintype U] [Fintype A] [Fintype S]
      [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S],
    N≤Fintype.card V→Fintype.card S≤s→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b:ℕ),1≤b→
    ∀ (src dst:A→V) (row:S→V) (φ:V→V) (u u':S→U) (jr:A→Bool) (js:S→Bool)
      (W Z:Finset V) (B:Finset U),
    ∀ D:MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W Z B,
    ∀ (I:Finset V),(W∪markedDiagramRows D)⊆I→
    ∀ (ψ:U→U) (F:SimpleGraph V) (A₀ B₀:U→Finset V) (q:U→ℝ),
    (∀ a,src a∈Z∧dst a∈Z∧φ (src a)∈Z∧φ (dst a)∈Z)→
    (∀ a,row a∈Z∧φ (row a)∈Z)→(∀ a,u a∈B∧u' a∈B)→
    (∀ a,u' a=ψ (u a))→(∀ a,u a≠u' a)→
    (∀ z,(Finset.univ.filter (fun a:{a:S // u a=z}=>js a.val=false)).card=
      (l+4)*(Finset.univ.filter (fun a:{a:S // u a=z}=>js a.val=true)).card)→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    Function.Injective (fun a=>if jr a then ({src a,π (dst a)}:Finset V) else {src a,dst a})→
    Function.Injective (fun a=>if jr a then ({φ (src a),π (φ (dst a))}:Finset V) else {φ (src a),φ (dst a)})→
    Function.Injective (fun a=>(row a,u a))→Function.Injective (fun a=>(φ (row a),u' a))→
    Disjoint (markedRootGraphResources π src dst row jr u)
      (markedRootGraphResources π (fun a=>φ (src a)) (fun a=>φ (dst a)) (fun a=>φ (row a)) jr u')→
    (I.card:ℝ)≤ε*Fintype.card V+F₀→
    (∀ v z,HK v z→¬H₀ v z)→(∀ v,(F.degree v:ℝ)≤dF)→
    (∀ z,(∃ a:S,u a=z)→q₀≤q z)→
    (∀ z,(∃ a:S,u a=z)→∀ v,v∈A₀ z↔HK v z∧HK v (ψ z))→
    (∀ z,(∃ a:S,u a=z)→∀ v∈B₀ z,H₀ v z∧H₀ v (ψ z))→
    (∀ z,(∃ a:S,u a=z)→|((A₀ z).card:ℝ)-q z*Fintype.card V|≤ε*Fintype.card V)→
    (∀ z,(∃ a:S,u a=z)→|((B₀ z).card:ℝ)-(l+4)*q z*Fintype.card V|≤ε*Fintype.card V)→
    (∀ z,(∃ a:S,u a=z)→((B₀ z∩(A₀ z).image π).card:ℝ)≤ε*Fintype.card V)→
    (∀ z,(∃ a:S,u a=z)→β*(Fintype.card V:ℝ)^(l+5)≤
      Fintype.card (ClassMarkedCycle tail head ktail khead (l+4) π b (A₀ z) (B₀ z)))→
    (∀ z,(∃ a:S,u a=z)→∀ j:Bool,∀ v v':V,v≠v'→β*(Fintype.card V:ℝ)^(l+4)≤
      Fintype.card (RootFirstCommonMarkedPath tail head ktail khead (l+4) π b
        (fun x (_:Unit)=>x∈B₀ z) (fun x (_:Unit)=>x∈A₀ z) j v v' () ()))→
    ∀ w:U→MarkedCycleTuple tail head ktail khead (l+4) π b→ℝ,
    (∀ z,(∃ a:S,u a=z)→∀ C,blo/(Fintype.card V:ℝ)^(l+4)≤w z C∧w z C≤bhi/(Fintype.card V:ℝ)^(l+4))→
    (∀ z,(∃ a:S,u a=z)→∀ j:Bool,∀ v:V,|1-resourceRootOmittedLoad typedMarkedCycleVertices (w z)
      (fun x=>x∈typedClassSet (A₀ z) (B₀ z)) (j,v)|≤ε)→
    ∃ Y T,Disjoint Y I∧Y.card≤s*((l+5)*t)∧
      (∀ x∈Y,∀ y∈Y,¬F.Adj x y)∧
      IsResourceTransformer (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
        (m:=l+4) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK))
        (markedRootGraphResources π src dst row jr u)
        (markedRootGraphResources π (fun a=>φ (src a)) (fun a=>φ (dst a)) (fun a=>φ (row a)) jr u') T∧
      (∀ e∈T,MarkedResourceSupported tail head ktail khead π (markedDiagramRows D∪Y) e)∧
      (∀ e∈T,¬MarkedOldResource tail head ktail khead π Z B e)∧
      ∀ v z,Sum.inr (v,z)∈T→z∈markedDiagramHubs D:=by
  obtain ⟨ε,hε,hchoose⟩:=marked_profile_transformer_completion (l+4) (by omega) q₀ β blo bhi hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro s
  obtain ⟨t,ht,hchoose⟩:=hchoose s
  refine ⟨t,ht,?_⟩
  intro F₀ dF hF₀ hdF
  obtain ⟨N,hchoose⟩:=hchoose F₀ dF hF₀ hdF s
  refine ⟨N,?_⟩
  intro V U E K A S _ _ _ _ _ _ _ _ hn hs tail head ktail khead H₀ HK π b hb src dst row φ u u' jr js W Z B D I hWI ψ F A₀ B₀ q
    hR hS hU hu' hune hbal hp hr hr' hsp hsp' hLL hW htypes hF hq hAK hBO hAc hBc hOc hbase hpath w hw hroot
  obtain ⟨ZK,ZO,hZ,hZW,hZZ,hZsep⟩:=marked_diagram_hub_profiles D ψ hu' htypes hbal
  obtain ⟨hP,hN,hid⟩:=marked_diagram_exact_identity (Nat.zero_le l) D hp ψ hu' hr hr' hsp hsp'
  obtain ⟨hPW,hNW⟩:=marked_diagram_supported D hR hS
  have hrootsp:=marked_diagram_opposite_spokes D ψ hu' hU hune hS
  let J:Type:={z:U // ∃ a:S,u a=z}
  have huJ:∀ z:J,z.val≠ψ z.val:=by
    intro z;obtain ⟨a,ha⟩:=z.property
    rw [←ha,←hu' a];exact hune a
  have hZJA:∀ z:J,ZK z.val⊆A₀ z.val:=by
    intro z v hv;exact (hAK z.val z.property v).mpr ((hZ z.val).2.2.2.2.1 v hv)
  have hZJW:∀ z:J,ZK z.val∪ZO z.val⊆I:=
    fun z v hv=>hWI (Finset.mem_union_right _ (hZW z.val hv))
  have hZJJ:∀ z z':J,z≠z'→Disjoint (ZK z.val∪ZO z.val) (ZK z'.val∪ZO z'.val):=
    fun z z' hne=>hZZ z.val z'.val (fun he=>hne (Subtype.ext he))
  have hspJ:∀ z:J,∀ v∈ZK z.val∪ZO z.val,
      (Sum.inr (v,ψ z.val):Finset V⊕(V×U))∉markedDiagramPlus D∧
      (Sum.inr (v,z.val):Finset V⊕(V×U))∉markedDiagramMinus D:=by
    intro z v hv;exact hrootsp z.val v ((hZ z.val).1 ▸ hv)
  have hidJ:∀ e:Finset V⊕(V×U),(if e∈markedDiagramPlus D then (1:ℤ) else 0)-(if e∈markedDiagramMinus D then 1 else 0)=
      (if e∈markedRootGraphResources π src dst row jr u then 1 else 0)-
      (if e∈markedRootGraphResources π (fun a=>φ (src a)) (fun a=>φ (dst a)) (fun a=>φ (row a)) jr u' then 1 else 0)+
      ∑ z:J,((if e∈(ZK z.val∪ZO z.val).image (fun v=>Sum.inr (v,z.val)) then 1 else 0)-
        (if e∈(ZK z.val∪ZO z.val).image (fun v=>Sum.inr (v,ψ z.val)) then 1 else 0)):=by
    intro e;rw [hid,marked_spoke_path_active_load]
    congr 1
    apply Finset.sum_congr rfl
    intro z _;rw [(hZ z.val).1]
  obtain ⟨Y,T,hY,hYc,hYF,hT,hTW,hnew⟩:=hchoose V U E K J hn ((marked_active_hub_card u).trans hs)
    tail head ktail khead π b hb H₀ HK F (fun z:J=>z.val) (fun z:J=>ψ z.val)
    (fun z:J=>A₀ z.val) (fun z:J=>B₀ z.val) (fun z:J=>ZK z.val) (fun z:J=>ZO z.val)
    I (fun z:J=>q z.val) huJ (fun z=>hq z.val z.property) htypes
    (fun z v hv=>(hAK z.val z.property v).mp hv) (fun z=>hBO z.val z.property)
    (fun z=>(hZ z.val).2.2.2.2.2) hZJA hZJW hZJJ (fun z=>hZsep z.val)
    (fun z=>(hZ z.val).2.2.1) (fun z=>((hZ z.val).2.2.2.1).trans hs) hW
    (fun z=>hAc z.val z.property) (fun z=>by simpa only [Nat.cast_add,Nat.cast_ofNat] using hBc z.val z.property) (fun z=>hOc z.val z.property)
    hp hF (fun z=>hbase z.val z.property) (fun z=>hpath z.val z.property)
    (fun z=>w z.val) (fun z=>hw z.val z.property) (fun z=>hroot z.val z.property)
    (markedDiagramPlus D) (markedDiagramMinus D)
    (markedRootGraphResources π src dst row jr u)
    (markedRootGraphResources π (fun a=>φ (src a)) (fun a=>φ (dst a)) (fun a=>φ (row a)) jr u')
    hLL hP hN
    (fun e he=>marked_resource_support_mono (Finset.subset_union_right.trans hWI) e (hPW e he))
    (fun e he=>marked_resource_support_mono (Finset.subset_union_right.trans hWI) e (hNW e he)) hspJ hidJ
  refine ⟨Y,T,hY,hYc,hYF,hT,?_,?_,?_⟩
  · intro e he
    by_cases hpe:e∈markedDiagramPlus D
    · exact marked_resource_support_mono Finset.subset_union_left e (hPW e hpe)
    obtain ⟨z,hz⟩:=hnew e he hpe
    have hsub:Y∪(ZK z.val∪ZO z.val)⊆markedDiagramRows D∪Y:=by
      intro v hv;rcases Finset.mem_union.mp hv with hv|hv
      · exact Finset.mem_union_right _ hv
      · exact Finset.mem_union_left _ (hZW z.val hv)
    exact marked_resource_support_mono hsub e (marked_switch_resource_supported _ _ _ _ e hz)
  · intro e he hold
    by_cases hpe:e∈markedDiagramPlus D
    · exact Finset.disjoint_left.mp hT.1 he (marked_diagram_plus_old_resources D hp e hpe hold)
    obtain ⟨z,hz⟩:=hnew e he hpe
    have hYZ:Disjoint Y Z:=hY.mono_right (fun v hv=>hWI (Finset.mem_union_right _ (marked_diagram_rows_root D hv)))
    have hZold:Disjoint (ZK z.val∪ZO z.val) Z:=by
      rw [(hZ z.val).1]
      apply Finset.disjoint_left.mpr
      intro v hv hvZ
      obtain ⟨a,_,hv⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hv
      exact (D.spokeAvoid a.val k).2.1 hvZ
    cases e with
    | inl e=>
      obtain ⟨a,ha,hat,hah,hYa⟩:=hz
      obtain ⟨a',ha',hZt,hZh⟩:=hold
      have haa:a=a':=hp (ha.trans ha'.symm)
      subst a'
      rcases hYa with hYa|hYa
      · exact Finset.disjoint_left.mp hYZ hYa hZt
      · exact Finset.disjoint_left.mp hYZ hYa hZh
    | inr vu=>
      exact Finset.disjoint_left.mp (Finset.disjoint_union_left.mpr ⟨hYZ,hZold⟩) hz.1 hold.1

  · intro v z he
    by_cases hpe:Sum.inr (v,z)∈markedDiagramPlus D
    · exact marked_diagram_plus_hubs D v z hpe
    obtain ⟨a,ha⟩:=hnew (Sum.inr (v,z)) he hpe
    obtain ⟨j,hj⟩:=a.property
    rcases ha.2 with hz|hz
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj.trans hz.symm⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,(hu' j).trans ((congrArg ψ hj).trans hz.symm)⟩))

end Oberwolfach
