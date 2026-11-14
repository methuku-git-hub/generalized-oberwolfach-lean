module

public import Oberwolfach.MarkedInitialDiagramConstruction
public import Oberwolfach.MarkedDiagramCompletion
public import Oberwolfach.MarkedDiagramGeometry
public import Oberwolfach.MarkedRootGraphSupport
public import Oberwolfach.DenseCommonNeighbourBounds

@[expose] public section

/-! The complete padded host transformer. Its initial diagram is constructed
from the explicit host counts and its hub factors from the original profiles.
No diagram, path, factor, transformer or absorber existence is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_padded_host_transformer (l:ℕ) (hl:2≤l)
    (q₀ β blo bhi:ℝ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ s:ℕ,∃ t:ℕ,1≤t∧∀ F₀ dF:ℝ,0≤F₀→0≤dF→∃ N:ℕ,
    ∀ (V U E K A S:Type) [Fintype V] [Fintype U] [Fintype A] [Fintype S]
      [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S],
    N≤Fintype.card V→Fintype.card S≤s→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b:ℕ),1≤b→
    ∀ (src dst:A→V) (row:S→V) (φ:V→V) (u u':S→U) (jr:A→Bool) (js:S→Bool)
      (W R R':Finset V) (B:Finset U) (c ch:ℝ),
    ∀(hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hRR:Disjoint R R')
    (hroots:∀ e,src e∈R∧dst e∈R∧φ (src e)∈R'∧φ (dst e)∈R')
    (hsroots:∀ s,row s∈R∧φ (row s)∈R') (hU:∀ s,u s∈B∧u' s∈B)
    (hvw:∀ e,¬PermutationClose π b (src e) (dst e))
    (hvw':∀ e,¬PermutationClose π b (φ (src e)) (φ (dst e)))
    (hfour:∀ e,∀ x∈({src e,dst e,φ (src e),φ (dst e)}:Finset V),
      ∀ y∈({src e,dst e,φ (src e),φ (dst e)}:Finset V),x≠y→¬PermutationClose π b x y)
    (hbal:∀ v,Fintype.card {e:A // dst e=v}=Fintype.card {e:A // src e=v}∧
      Fintype.card {e:A // dst e=v}=Fintype.card {s:S // row s=v})
    (hmark:∀ v,(Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=
      (Finset.univ.filter (fun s:{s:S // row s=v}=>js s.val=true)).card)
    (hpad:∀ v,¬(Fintype.card {e:A // dst e=v}=1∧
      (Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=1))
    (hr:Function.Injective (fun e=>if jr e then ({src e,π (dst e)}:Finset V) else {src e,dst e}))
    (hr':Function.Injective (fun e=>if jr e then ({φ (src e),π (φ (dst e))}:Finset V) else {φ (src e),φ (dst e)}))
    (hs:Function.Injective (fun s=>(row s,u s))) (hs':Function.Injective (fun s=>(φ (row s),u' s)))
    (hroot:∀ e,if jr e then (∃ k,ktail k=src e∧khead k=dst e)∧(∃ k,ktail k=φ (src e)∧khead k=φ (dst e))
      else (∃ k,tail k=src e∧head k=dst e)∧(∃ k,tail k=φ (src e)∧head k=φ (dst e)))
    (hropen:∀ e,c≤((Finset.univ.filter (fun a=>(∃ k,tail k=dst e∧head k=a)∧(∃ k,tail k=φ (dst e)∧head k=a))).card:ℝ))
    (hrclose:∀ e,c≤((Finset.univ.filter (fun a=>(∃ k,tail k=a∧head k=src e)∧(∃ k,tail k=a∧head k=φ (src e)))).card:ℝ))
    (hrstep:∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)).card:ℝ))
    (hrjoin:∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧(∃ e,tail e=a∧head e=y))).card:ℝ))
    (hsroot:∀ s,if js s then HK (row s) (u s)∧HK (φ (row s)) (u' s) else H₀ (row s) (u s)∧H₀ (φ (row s)) (u' s))
    (hsopen:∀ s,c≤((Finset.univ.filter (fun a=>(∃ e,tail e=row s∧head e=a)∧
      (∃ e,tail e=φ (row s)∧head e=a)∧H₀ a (u s)∧H₀ a (u' s))).card:ℝ))
    (hsclose:∀ s,c≤((Finset.univ.filter (fun a=>(if js s then
      (∃ e,ktail e=a∧khead e=row s)∧(∃ e,ktail e=a∧khead e=φ (row s)) else
      (∃ e,tail e=a∧head e=row s)∧(∃ e,tail e=a∧head e=φ (row s)))∧H₀ a (u s)∧H₀ a (u' s))).card:ℝ))
    (hsstep:∀ s,∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun a=>
      (if t then ∃ e,ktail e=x∧khead e=a else ∃ e,tail e=x∧head e=a)∧
      (if t then HK a (u s)∧HK a (u' s) else H₀ a (u s)∧H₀ a (u' s)))).card:ℝ))
    (hsjoin:∀ s,∀ x y,x≠y→c≤((Finset.univ.filter (fun a=>(∃ e,tail e=x∧head e=a)∧
      (∃ e,tail e=a∧head e=y)∧H₀ a (u s)∧H₀ a (u' s))).card:ℝ))
    (hvstep:∀ u:U,∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun y=>
      (if t then ∃ e,ktail e=x∧khead e=y else ∃ e,tail e=x∧head e=y)∧
      (if t then HK y u else H₀ y u))).card:ℝ))
    (hvjoin:∀ u:U,∀ x y,x≠y→c≤((Finset.univ.filter (fun q=>(∃ e,tail e=x∧head e=q)∧
      (∃ e,tail e=q∧head e=y)∧H₀ q u)).card:ℝ))
    (hhcount:∀ A Q:Finset V,Disjoint A Q→A.card+Q.card≤l+11→
      (∀ x∈A∪Q,∀ y∈A∪Q,x≠y→¬PermutationClose π b x y)→
      ch≤((Finset.univ.filter (fun u=>(∀ x∈A,H₀ x u)∧∀ x∈Q,HK x u)).card:ℝ))
    (hhbudget:B.card+Fintype.card A<ch)
    (hbudget:W.card+(2*((Fintype.card A:ℝ)*(l+3)+Fintype.card S*(l+4))+
      2*Fintype.card A*(l+4)+(R∪R').card+l+5)*(2*b+1)<c),
    ∀ (ψ:U→U) (F:SimpleGraph V) (A₀ B₀:U→Finset V) (q:U→ℝ),
    (∀ a,u' a=ψ (u a))→(∀ a,u a≠u' a)→
    (∀ z,(Finset.univ.filter (fun a:{a:S // u a=z}=>js a.val=false)).card=
      (l+4)*(Finset.univ.filter (fun a:{a:S // u a=z}=>js a.val=true)).card)→
    (W.card:ℝ)+((R∪R').card+(Fintype.card A:ℝ)*(l+3)+Fintype.card S*(l+4)+2*Fintype.card A*(l+4))*(dF+1)≤ε*Fintype.card V+F₀→
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
    ∃ X Y T,∃ H:Finset U,
      X.card≤(R∪R').card+Fintype.card A*(l+3)+Fintype.card S*(l+4)+2*Fintype.card A*(l+4)∧
      (R∪R')⊆X∧
      Disjoint (X\(R∪R')) W∧
      (∀ x∈X\(R∪R'),∀ y∈R∪R',¬PermutationClose π b x y)∧
      (∀ x∈X\(R∪R'),∀ y∈X\(R∪R'),x≠y→¬PermutationClose π b x y)∧
      Disjoint Y (W∪X)∧Y.card≤s*((l+5)*t)∧
      (∀ x∈Y,∀ y∈Y,¬F.Adj x y)∧(∀ x∈Y,∀ y∈X,¬F.Adj x y)∧
      IsResourceTransformer (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
        (m:=l+4) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK))
        (markedRootGraphResources π src dst row jr u)
        (markedRootGraphResources π (fun a=>φ (src a)) (fun a=>φ (dst a)) (fun a=>φ (row a)) jr u') T∧
      (∀ e∈T,MarkedResourceSupported tail head ktail khead π (X∪Y) e)∧
      (∀ e∈T,¬MarkedOldResource tail head ktail khead π (R∪R') B e)∧
      H.card≤2*Fintype.card S+Fintype.card A∧
      (∀ v z,Sum.inr (v,z)∈T→z∈H)∧
      ∀ z∈H,z∈B→∃ a:S,u a=z∨u' a=z :=by
  obtain ⟨ε,hε,hchoose⟩:=marked_diagram_completion l q₀ β blo bhi hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro s
  obtain ⟨t,ht,hchoose⟩:=hchoose s
  refine ⟨t,ht,?_⟩
  intro F₀ dF hF₀ hdF
  obtain ⟨N,hchoose⟩:=hchoose F₀ dF hF₀ hdF
  refine ⟨N,?_⟩
  intro V U E K A S _ _ _ _ _ _ _ _ hn hsbound tail head ktail khead H₀ HK π b hb src dst row φ u u' jr js W R R' B c ch
    hp hRR hroots hsroots hU hvw hvw' hfour hbal hmark hpad hr hr' hs hs' hroot hropen hrclose hrstep hrjoin
    hsroot hsopen hsclose hsstep hsjoin hvstep hvjoin hhcount hhbudget hbudget
    ψ F A₀ B₀ q hu' hune hhubbal hnum htypes hF hq hAK hBO hAc hBc hOc hbase hpath w hw hrootload
  obtain ⟨D⟩:=marked_initial_diagram_construction tail head ktail khead H₀ HK π b l hl src dst row φ u u' jr js
    W R R' B c ch hp hRR hroots hsroots hU hvw hvw' hfour hbal hmark hpad hr hr' hs hs' hroot hropen hrclose
    hrstep hrjoin hsroot hsopen hsclose hsstep hsjoin hvstep hvjoin hhcount hhbudget hbudget
  let X:=markedDiagramRows D
  let I:=W∪(X∪X.biUnion (fun v=>F.neighborFinset v))
  have hXI:W∪X⊆I:=by
    intro v hv;rcases Finset.mem_union.mp hv with hv|hv
    · exact Finset.mem_union_left _ hv
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hv)
  have hXc:X.card≤(R∪R').card+Fintype.card A*(l+3)+Fintype.card S*(l+4)+2*Fintype.card A*(l+4):=
    marked_diagram_rows_card D
  have hIcard:(I.card:ℝ)≤ε*Fintype.card V+F₀:=by
    have hx:(X.card:ℝ)≤(R∪R').card+Fintype.card A*(l+3)+Fintype.card S*(l+4)+2*Fintype.card A*(l+4):=by
      exact_mod_cast hXc
    have hx':=(mul_le_mul_of_nonneg_right hx (show 0≤dF+1 by linarith))
    have hN:=forbidden_used_neighbours_card F X dF hF
    have hi:(I.card:ℝ)≤W.card+(X∪X.biUnion (fun v=>F.neighborFinset v)).card:=by
      exact_mod_cast Finset.card_union_le W (X∪X.biUnion (fun v=>F.neighborFinset v))
    linarith only [hx',hN,hi,hnum]
  have hroot₁:∀ a,if jr a then ∃ k,ktail k=src a∧khead k=dst a else ∃ e,tail e=src a∧head e=dst a:=by
    intro a;have hh:=hroot a;cases hj:jr a <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    all_goals exact hh.1
  have hroot₂:∀ a,if jr a then ∃ k,ktail k=φ (src a)∧khead k=φ (dst a) else ∃ e,tail e=φ (src a)∧head e=φ (dst a):=by
    intro a;have hh:=hroot a;cases hj:jr a <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    all_goals exact hh.2
  have hL₁:=marked_root_graph_old_supported (π:=π) src dst row jr u R B (fun a=>⟨(hroots a).1,(hroots a).2.1⟩)
    (fun a=>⟨(hsroots a).1,(hU a).1⟩) hroot₁
  have hL₂:=marked_root_graph_old_supported (π:=π) (fun a=>φ (src a)) (fun a=>φ (dst a)) (fun a=>φ (row a)) jr u' R' B
    (fun a=>⟨(hroots a).2.2.1,(hroots a).2.2.2⟩) (fun a=>⟨(hsroots a).2,(hU a).2⟩) hroot₂
  have hLL:=marked_resource_sets_disjoint hp R R' hRR _ _ (fun e he=>(hL₁ e he).2) (fun e he=>(hL₂ e he).2)
  have hRZ:∀ a,src a∈R∪R'∧dst a∈R∪R'∧φ (src a)∈R∪R'∧φ (dst a)∈R∪R':=fun a=>
    ⟨Finset.mem_union_left _ (hroots a).1,Finset.mem_union_left _ (hroots a).2.1,
      Finset.mem_union_right _ (hroots a).2.2.1,Finset.mem_union_right _ (hroots a).2.2.2⟩
  have hSZ:∀ a,row a∈R∪R'∧φ (row a)∈R∪R':=fun a=>
    ⟨Finset.mem_union_left _ (hsroots a).1,Finset.mem_union_right _ (hsroots a).2⟩
  obtain ⟨Y,T,hY,hYc,hYF,hT,hTs,hTold,hThub⟩:=hchoose V U E K A S hn hsbound tail head ktail khead H₀ HK π b hb
    src dst row φ u u' jr js W (R∪R') B D I hXI ψ F A₀ B₀ q hRZ hSZ hU hu' hune hhubbal
    hp hr hr' hs hs' hLL hIcard htypes hF hq hAK hBO hAc hBc hOc hbase hpath w hw hrootload
  have hXfree:X\(R∪R')⊆markedDiagramFreeRows D:=by
    intro v hv
    have hh: v∈(R∪R')∪markedDiagramFreeRows D:=by rw [←marked_diagram_rows_eq D];exact (Finset.mem_sdiff.mp hv).1
    exact (Finset.mem_union.mp hh).resolve_left (Finset.mem_sdiff.mp hv).2
  have hfree:=marked_diagram_free_rows_separated D
  refine ⟨X,Y,T,markedDiagramHubs D,hXc,(fun v hv=>marked_diagram_rows_root D hv),(marked_diagram_free_rows_avoid D).mono hXfree Finset.subset_union_left,
    (fun x hx=>hfree.1 x (hXfree hx)),(fun x hx y hy=>hfree.2 x (hXfree hx) y (hXfree hy)),
    hY.mono_right hXI,hYc,hYF,?_,hT,hTs,hTold,marked_diagram_hubs_card D,hThub,marked_diagram_hubs_old D⟩
  intro x hx y hy hxy
  exact Finset.disjoint_left.mp hY hx (Finset.mem_union_right _ (Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨y,hy,(F.mem_neighborFinset y x).mpr hxy.symm⟩)))

end Oberwolfach
