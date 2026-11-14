module

public import Oberwolfach.MarkedInitialDiagramData
public import Oberwolfach.MarkedRowAssignmentTypes

@[expose] public section

/-! Construct the complete initial marked diagram from the host counts
and the padded root graph. Every wheel, path, hub and assignment in the
result is chosen here; both physical packings are proved at this caller. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
  [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]

theorem marked_initial_diagram_construction
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (b l:ℕ) (hl:2≤l) (src dst:A→V) (row:S→V) (φ:V→V)
    (u u':S→U) (jr:A→Bool) (js:S→Bool) (W R R':Finset V) (B:Finset U) (c ch:ℝ)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
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
      2*Fintype.card A*(l+4)+(R∪R').card+l+5)*(2*b+1)<c):
    Nonempty (MarkedInitialDiagram tail head ktail khead H₀ HK π b l src dst row φ u u' jr js W (R∪R') B):=by
  let Z:=R∪R'
  have hrootZ:∀ e,src e∈Z∧dst e∈Z∧φ (src e)∈Z∧φ (dst e)∈Z:=fun e=>
    ⟨Finset.mem_union_left _ (hroots e).1,Finset.mem_union_left _ (hroots e).2.1,
      Finset.mem_union_right _ (hroots e).2.2.1,Finset.mem_union_right _ (hroots e).2.2.2⟩
  have hsrootZ:∀ s,row s∈Z∧φ (row s)∈Z:=fun s=>
    ⟨Finset.mem_union_left _ (hsroots s).1,Finset.mem_union_right _ (hsroots s).2⟩
  have hnonneg:0≤(Fintype.card A:ℝ)*(l+3)+Fintype.card S*(l+4)+2*Fintype.card A*(l+4):=by positivity
  have hbc:0≤(2*b+1:ℝ):=by positivity
  have hip:W.card+((Fintype.card A:ℝ)*(l+3)+Fintype.card S*(l+4)+Z.card+l+5)*(2*b+1)<c:=by
    dsimp only [Z]
    nlinarith only [hbudget,hbc,hnonneg]
  obtain ⟨pr,ps,C,D,SC,SD,hC,hD,hSh,hSC,hSD,hrav,hsav,hrdis,hsdis,hrs,hrcross,hscross,hrscross⟩:=
    marked_initial_paths tail head ktail khead H₀ HK π b l hl src dst
      (fun e=>φ (src e)) (fun e=>φ (dst e)) jr row (fun s=>φ (row s)) u u' js W Z c
      hrootZ hsrootZ hvw hvw' hroot hropen hrclose hrstep hrjoin hsroot hsopen hsclose hsstep hsjoin hip
  obtain ⟨τ,a,d,hτ,hjin,hjout⟩:=marked_row_assignment_types src dst row jr js hbal hmark hpad
  let P:=markedPathUnion (l+3) (l+4) (fun e=>pr e) (fun s=>ps s)
  have hrP:=markedPathUnion_rim (l+3) (l+4) (fun e=>pr e) (fun s=>ps s)
  have hsP:=markedPathUnion_spoke (l+3) (l+4) (fun e=>pr e) (fun s=>ps s)
  have hPZ:Disjoint P Z:=markedPathUnion_avoid (l+3) (l+4) (fun e=>pr e) (fun s=>ps s) Z
    (fun e k=>(hrav e k).2.1) (fun s k=>(hsav s k).2.1)
  have hPP:=markedPathUnion_separated (l+3) (l+4) (fun e=>pr e) (fun s=>ps s) π b hrcross hscross hrscross
  have hPZsep:=markedPathUnion_root_separated (l+3) (l+4) (fun e=>pr e) (fun s=>ps s) π b Z
    (fun e k=>(hrav e k).2.2) (fun s k=>(hsav s k).2.2)
  have hloop:∀ e,dst e≠src e:=fun e he=>hvw e (Or.inl he.symm)
  have hloop':∀ e,φ (dst e)≠φ (src e):=fun e he=>hvw' e (Or.inl he.symm)
  have hcross:∀ e,src e≠φ (src e)∧src e≠φ (dst e)∧dst e≠φ (src e)∧dst e≠φ (dst e):=by
    intro e
    have hh:∀ x∈R,∀ y∈R',x≠y:=fun x hx y hy he=>Finset.disjoint_left.mp hRR hx (he ▸ hy)
    exact ⟨hh _ (hroots e).1 _ (hroots e).2.2.1,hh _ (hroots e).1 _ (hroots e).2.2.2,
      hh _ (hroots e).2.1 _ (hroots e).2.2.1,hh _ (hroots e).2.1 _ (hroots e).2.2.2⟩
  obtain ⟨hub,RC,RD,hB,hR,hsp⟩:=marked_attachment_hub_construction tail head ktail khead H₀ HK π b (l+2)
    src dst row φ hloop a d τ hτ pr ps (fun e=>canonicalMarkedRotation (if jr e then 0 else 3)) C D hC hD
    Z P B ch hrootZ hcross hrP hsP hPZ hPP hPZsep hfour hrdis hrs hhcount hhbudget
  have hRC:∀ e i,(RC e).1.val i=Fin.cons (α:=fun _=>V) (src e) (Fin.cons (dst e) (pr e))
      (canonicalMarkedRotation (if jr e then 0 else 3) i):=by
    intro e i;rw [(hR e).1];exact hC e i
  have hRD:∀ e i,(RD e).1.val i=Fin.cons (α:=fun _=>V) (φ (src e)) (Fin.cons (φ (dst e)) (pr e))
      (canonicalMarkedRotation (if jr e then 0 else 3) i):=by
    intro e i;rw [(hR e).2.1];exact hD e i
  have hPc:(P.card:ℝ)≤Fintype.card A*(l+3)+Fintype.card S*(l+4):=by
    exact_mod_cast markedPathUnion_card (l+3) (l+4) (fun e=>pr e) (fun s=>ps s)
  have hWP:((W∪P).card:ℝ)≤W.card+P.card:=by exact_mod_cast Finset.card_union_le W P
  have hvb:(W∪P).card+(2*(Fintype.card A:ℝ)*((l+1)+3)+Z.card+P.card+(l+1)+4)*(2*b+1)<c:=by
    have hb1:(1:ℝ)≤2*b+1:=by have hb0:0≤(b:ℝ):=Nat.cast_nonneg b;linarith
    dsimp only [Z] at *
    nlinarith only [hbudget,hPc,hWP,hbc,hb1]
  obtain ⟨pv,VC,VD,hends,hVC,hVD,hVav,hVnew,hVP,hVsep,hVdis,hVcross,hVPsep⟩:=
    marked_vertex_wheel_construction tail head ktail khead H₀ HK π b (l+1) (by omega)
      src dst row φ jr js a d τ hjin hjout pr ps hub RC RD SC SD hRC hRD
      (fun e=>(hR e).2.2.1) (fun e=>(hR e).2.2.2) hSC hSD (W∪P) Z P hPZ Finset.subset_union_right
      hrootZ hrP hsP hPP hPZsep hrdis hsdis hrs hsp c hvstep hvjoin
      (by simpa only [Nat.cast_add,Nat.cast_one] using hvb)
  have hvin:∀ v e,pv ⟨v,Sum.inl e⟩ 0=pr e.val 0∧
      pv ⟨v,Sum.inl e⟩ (Fin.last (l+3))=ps (a v e).val (Fin.last (l+3)):=fun v e=>
    ⟨(hends ⟨v,Sum.inl e⟩).1,(hends ⟨v,Sum.inl e⟩).2.1⟩
  have hvout:∀ v e,pv ⟨v,Sum.inr e⟩ 0=ps (d v e).val 0∧
      pv ⟨v,Sum.inr e⟩ (Fin.last (l+3))=pr e.val (Fin.last (l+2)):=fun v e=>
    ⟨(hends ⟨v,Sum.inr e⟩).1,(hends ⟨v,Sum.inr e⟩).2.1⟩
  have hvnew:∀ z k,pv z k∈W∪P→pv z k∈({pv z 0,pv z (Fin.last (l+3))}:Finset V):=by
    intro z k hk
    simpa only [←(hends z).1,←(hends z).2.1] using hVnew z k hk
  have hvP:∀ z k,pv z k∉R∪R'∧(pv z k∈P→pv z k∈({pv z 0,pv z (Fin.last (l+3))}:Finset V)):=by
    intro z k
    exact ⟨(hVav z k).1,fun hk=>hvnew z k (Finset.mem_union_right _ hk)⟩
  have hplus:=marked_constructed_family_packing (l+1) (by omega) hp src dst row id φ hub u jr js
    (fun z=>markedIncidenceSpokeType jr (τ z.1 z.2)) a d τ hτ pr ps pv RC SC VD hRC hSC hVD
    (fun e=>(hR e).2.2.1) (fun s=>(hSh s).1) (fun z=>(hends z).2.2.2) hvin hvout
    R R' P hRR hPZ hroots (fun s=>(hsroots s).1) hrP hsP hvP hrdis hsdis hVdis hrs hub.injective
    (fun e s he=>hB e (he ▸ (hU s).1)) hloop' hr hs
  have hminus:=marked_constructed_family_packing (l+1) (by omega) hp src dst row φ id hub u' jr js
    (fun z=>markedIncidenceSpokeType jr (τ z.1 z.2)) a d τ hτ pr ps pv RD SD VC hRD hSD hVC
    (fun e=>(hR e).2.2.2) (fun s=>(hSh s).2) (fun z=>(hends z).2.2.1) hvin hvout
    R' R P hRR.symm (by simpa only [Finset.union_comm] using hPZ)
    (fun e=>⟨(hroots e).2.2.1,(hroots e).2.2.2,(hroots e).1,(hroots e).2.1⟩)
    (fun s=>(hsroots s).2) hrP hsP (by simpa only [Finset.union_comm] using hvP)
    hrdis hsdis hVdis hrs hub.injective (fun e s he=>hB e (he ▸ (hU s).2)) hloop hr' hs'
  exact ⟨{
    a:=a,d:=d,τ:=τ,deranged:=hτ,incomingType:=hjin,outgoingType:=hjout
    pr:=pr,ps:=ps,pv:=pv,hub:=hub,freshHub:=hB,RC:=RC,RD:=RD,SC:=SC,SD:=SD,VC:=VC,VD:=VD
    rimCoordinates:=hRC,imageRimCoordinates:=hRD,rimHubs:=fun e=>⟨(hR e).2.2.1,(hR e).2.2.2⟩
    spokeCoordinates:=hSC,imageSpokeCoordinates:=hSD,spokeHubs:=hSh
    vertexCoordinates:=hVC,imageVertexCoordinates:=hVD,vertexHubs:=fun z=>⟨(hends z).2.2.1,(hends z).2.2.2⟩
    vertexEnds:=fun z=>⟨(hends z).1,(hends z).2.1⟩
    rimAvoid:=hrav,spokeAvoid:=hsav,vertexAvoid:=hVav,vertexNewAvoid:=hvnew
    rimDisjoint:=hrdis,spokeDisjoint:=hsdis,vertexDisjoint:=hVdis,rimSpokeDisjoint:=hrs
    pathSeparated:=hPP,vertexSeparated:=hVcross,vertexPathSeparated:=hVPsep
    plusPacking:=hplus,minusPacking:=hminus}⟩

end Oberwolfach
