module

public import Oberwolfach.MarkedTerminalAbsorberProperty
public import Oberwolfach.MarkedDecompositionSubhost
public import Oberwolfach.MarkedRemainderSubhost

@[expose] public section

/-! A terminal absorber chosen inside a sampled typed subhost is viewed
in the ambient host. Its later remainder is specified by ambient arc
identifiers, with explicit membership in the sampled terminal host.
The absorber is chosen before that remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

 theorem marked_terminal_absorber_in_ambient_host
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (PE:E→Prop) (PK:K→Prop) (PS:V×U→Prop) (b l s a₀ b₀ e₀ f:ℕ)
    (habs:MarkedTerminalAbsorberProperty
      (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val)
      (fun v u=>H₀ v u∧PS (v,u)) (fun v u=>HK v u∧PS (v,u)) π b l s a₀ b₀ e₀ f)
    (X:Finset V) (Z:Finset U) (hs:X.card+Z.card≤s)
    (F₀:Finset (Finset V⊕(V×U))) (hF:F₀.card≤f):
    ∃ C:MarkedSupportedEdgeSet
      (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) π U,
      Disjoint C.edges F₀∧C.edges.card≤e₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ e∈C.edges,¬MarkedOldResource
        (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) π X Z e)∧
      HasResourceDecomposition
        (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W) C.edges∧
      ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
        (∀ a∈A,Sum.elim PE PK a∧Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)→
        (∀ z∈S,(H₀ z.1 z.2∨HK z.1 z.2)∧PS z∧z.1∈X∧z.2∈Z)→
        MarkedRemainderDivisible tail head ktail khead HK A S (l+4)→
        HasResourceDecomposition
          (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W)
          (C.edges∪(A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr)):=by
  let src:=Sum.elim (fun e:{e // PE e}=>tail e.val) (fun e:{e // PK e}=>ktail e.val)
  let dst:=Sum.elim (fun e:{e // PE e}=>head e.val) (fun e:{e // PK e}=>khead e.val)
  let A₀:=Finset.univ.filter (fun a=>src a∈X∧dst a∈X)
  let S₀:=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧PS z∧z.1∈X∧z.2∈Z)
  have hrows:markedRemainderRows
      (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) A₀ S₀⊆X:=by
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · rcases Finset.mem_union.mp hv with hv|hv
      · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp ha).2.1
      · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp ha).2.2
    · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hz).2.2.2.1
  have hhubs:markedRemainderHubs S₀⊆Z:=by
    intro u hu
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hu
    exact (Finset.mem_filter.mp hz).2.2.2.2
  have hsp:∀ z∈S₀,(H₀ z.1 z.2∧PS (z.1,z.2))∨(HK z.1 z.2∧PS (z.1,z.2)):=by
    intro z hz
    obtain ⟨hh,hp,_,_⟩:=(Finset.mem_filter.mp hz).2
    exact hh.elim (fun h=>Or.inl ⟨h,hp⟩) (fun h=>Or.inr ⟨h,hp⟩)
  obtain ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,hCabs⟩:=habs X Z hs F₀ hF A₀ S₀ hrows hhubs hsp
  let lift:=fun W:MarkedWheel
      (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) (l+4) π b
      (fun v u=>H₀ v u∧PS (v,u)) (fun v u=>HK v u∧PS (v,u))=>
    markedWheelToLarger PE PK (fun _ _ h=>h.1) (fun _ _ h=>h.1) W
  have hlift (W):markedWheelPhysicalResources (lift W)=markedWheelPhysicalResources W:=
    markedWheelToLarger_resources PE PK _ _ W
  refine ⟨C,hCF,hCe,hCr,hCu,hCold,resource_decomposition_map _ _ lift hlift _ hCdec,?_⟩
  intro A S hA hS hdiv
  obtain ⟨A',hA'⟩:=marked_remainder_restrict_arcs PE PK A (fun a ha=>(hA a ha).1)
  let forget:{e // PE e}⊕{e // PK e}→E⊕K:=Sum.map Subtype.val Subtype.val
  have hsrc (a):Sum.elim tail ktail (forget a)=src a:=by cases a <;> rfl
  have hdst (a):Sum.elim head khead (forget a)=dst a:=by cases a <;> rfl
  have hAA:A'⊆A₀:=by
    intro a ha
    have haA:forget a∈A:=by rw [←hA'];exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
    · simpa only [hsrc] using (hA _ haA).2.1
    · simpa only [hdst] using (hA _ haA).2.2
  have hSS:S⊆S₀:=by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hS z hz⟩
  have hdiv':MarkedRemainderDivisible
      (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val)
      (fun v u=>HK v u∧PS (v,u)) A' S (l+4):=by
    apply (marked_remainder_divisible_subhost_iff PE PK PS A' S (fun z hz=>(hS z hz).2.1)).mpr
    rwa [hA']
  have hdec:=(hCabs A' hAA S hSS hdiv').2.2
  have he:(A'.image (fun a=>Sum.inl (β:=V×U) (markedPhysicalEdge
      (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) π a)))=
      A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a)):=by
    rw [←hA',Finset.image_image]
    apply Finset.image_congr
    intro a _
    cases a <;> rfl
  rw [he] at hdec
  exact resource_decomposition_map _ _ lift hlift _ hdec

end Oberwolfach
