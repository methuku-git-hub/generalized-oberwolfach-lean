module

public import Oberwolfach.MarkedUnusedIncidenceBounds
public import Oberwolfach.MarkedPackingTransport

@[expose] public section

/-! Unused outside resources are counted in the host actually supplied to
approximate packing. The reserved resources are not added to its remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {H₀ HK H₀' HK':V→U→Prop}

theorem marked_restricted_unused_card (PE:E→Prop) (PK:K→Prop)
    (hH₀:∀ x u,H₀' x u→H₀ x u) (hHK:∀ x u,HK' x u→HK x u)
    (B:Finset (Finset V⊕(V×U))) (x:V⊕U):
    (((markedIncidentEdges (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' HK' false x).filter
      (fun e=>markedActivePhysical (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' HK' e∉B)).card)=
    (((markedIncidentEdges tail head ktail khead π H₀ HK false x).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∉B∧markedActiveRetained PE PK H₀' HK' e)).card):=by
  classical
  let f:=markedActiveToLarger PE PK hH₀ hHK
  let S:=(markedIncidentEdges (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' HK' false x).filter
      (fun e=>markedActivePhysical (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' HK' e∉B)
  have he:S.image f=(markedIncidentEdges tail head ktail khead π H₀ HK false x).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ HK e∉B∧markedActiveRetained PE PK H₀' HK' e):=by
    ext e
    constructor
    · intro he
      obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he
      obtain ⟨ha,hB⟩:=Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_,?_⟩
      · exact (markedActiveToLarger_incident PE PK hH₀ hHK false x a).mpr (Finset.mem_filter.mp ha).2
      · simpa only [f,markedActiveToLarger_physical] using hB
      · exact (markedActiveToLarger_range PE PK hH₀ hHK _).mp ⟨a,rfl⟩
    · intro he
      obtain ⟨he,hB,hkeep⟩:=Finset.mem_filter.mp he
      obtain ⟨a,rfl⟩:=(markedActiveToLarger_range PE PK hH₀ hHK e).mpr hkeep
      refine Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩,rfl⟩
      · exact (markedActiveToLarger_incident PE PK hH₀ hHK false x a).mp (Finset.mem_filter.mp he).2
      · simpa only [markedActiveToLarger_physical] using hB
  have hc:=congrArg Finset.card he
  rw [Finset.card_image_of_injective _ (markedActiveToLarger_injective PE PK hH₀ hHK)] at hc
  exact hc

theorem marked_restricted_unused_bounds {m b:ℕ} (PE:E→Prop) (PK:K→Prop)
    (hH₀:∀ x u,H₀' x u→H₀ x u) (hHK:∀ x u,HK' x u→HK x u)
    (M:Finset (MarkedWheel (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' HK'))
    (A:Finset (E⊕K)) (S:Finset (V×U)) (δ:ℝ)
    (hA:∀ a∈A,Sum.elim PE PK a∧Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉M.biUnion markedWheelPhysicalResources)
    (hS:∀ z∈S,(H₀' z.1 z.2∨HK' z.1 z.2)∧Sum.inr z∉M.biUnion markedWheelPhysicalResources)
    (hleft:∀ x:V⊕U,((markedIncidentEdges (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' HK' false x\M.biUnion markedActiveResources).card:ℝ)≤δ):
    (∀ v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤δ)∧
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤δ)∧
    (∀ u,((S.filter (fun z=>u=z.2)).card:ℝ)≤δ)∧
    (A.card:ℝ)≤δ*Fintype.card V∧(S.card:ℝ)≤δ*Fintype.card V∧
    Disjoint (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr)
      (M.biUnion markedWheelPhysicalResources):=by
  apply marked_unused_incidence_bounds (M.biUnion markedWheelPhysicalResources) A S δ
    (markedActiveRetained PE PK H₀' HK')
  · intro a ha
    refine ⟨(hA a ha).2,?_⟩
    cases a <;> exact (hA _ ha).1
  · intro z hz
    have hp:= (hS z hz).1
    exact ⟨hp.elim (fun h=>Or.inl (hH₀ _ _ h)) (fun h=>Or.inr (hHK _ _ h)),(hS z hz).2,hp⟩
  · intro x
    rw [←marked_restricted_unused_card PE PK hH₀ hHK]
    convert hleft x using 1
    congr 1
    congr 1
    ext e
    simp only [Finset.mem_sdiff,Finset.mem_filter,Finset.mem_biUnion,markedActiveResources,
      Finset.mem_univ,true_and]
end Oberwolfach
