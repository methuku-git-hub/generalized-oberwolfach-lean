module

public import Oberwolfach.MarkedWheelResources
public import Oberwolfach.OrdinaryCycleWeightRestriction

@[expose] public section

/-! Restriction to subsets of the two rim types and the two spoke types.
The cycle tuple, hub, permutation, separation and coefficients are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m b : ℕ} {π : Equiv.Perm V}
  {H₀ Hₖ H₀' Hₖ' : V → U → Prop}

theorem markedCyclePhysicalEdge_at
    (C : MarkedCycleTuple tail head ktail khead m π b) (i : Fin (m+1)) :
    markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b C i)=
      if i=Fin.last m then {C.val i,π (C.val 0)} else {C.val i,C.val (finRotate (m+1) i)} := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [markedCycleTypedEdge,Fin.snoc_last,markedPhysicalEdge,Sum.elim_inr,ite_true]
    rw [(Classical.choose_spec C.property.2.2).1,(Classical.choose_spec C.property.2.2).2]
  · simp only [markedCycleTypedEdge,Fin.snoc_castSucc,markedPhysicalEdge,Sum.elim_inl,
      Fin.castSucc_ne_last,ite_false,finRotate_castSucc_eq_succ]
    rw [(Classical.choose_spec (C.property.2.1 j)).1,(Classical.choose_spec (C.property.2.1 j)).2]

def markedCycleToLarger (PE : E → Prop) (PK : K → Prop)
    (C : MarkedCycleTuple (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b) :
    MarkedCycleTuple tail head ktail khead m π b :=
  ⟨C.val,C.property.1,(fun j=>by obtain ⟨e,he⟩ := C.property.2.1 j;exact ⟨e.val,he⟩),
    by obtain ⟨e,he⟩ := C.property.2.2;exact ⟨e.val,he⟩⟩

theorem markedCycleToLarger_physical (PE : E → Prop) (PK : K → Prop)
    (C : MarkedCycleTuple (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b) :
    markedCyclePhysicalEdges tail head ktail khead m π b (markedCycleToLarger PE PK C)=
      markedCyclePhysicalEdges (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b C := by
  unfold markedCyclePhysicalEdges
  apply Finset.image_congr
  intro i _
  simp only [Function.comp_apply,markedCyclePhysicalEdge_at,markedCycleToLarger]

def markedWheelToLarger (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (W : MarkedWheel (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ') :
    MarkedWheel tail head ktail khead m π b H₀ Hₖ :=
  ⟨markedCycleToLarger PE PK W.1,⟨W.2.val,hHₖ _ _ W.2.property.1,
    fun i=>hH₀ _ _ (W.2.property.2 i)⟩⟩

theorem markedWheelToLarger_resources (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (W : MarkedWheel (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ') :
    markedWheelPhysicalResources (markedWheelToLarger PE PK hH₀ hHₖ W)=markedWheelPhysicalResources W := by
  dsimp only [markedWheelPhysicalResources,markedWheelToLarger]
  rw [markedCycleToLarger_physical]
  rfl

def MarkedWheelSurvives (PE : E → Prop) (PK : K → Prop)
    (H₀' Hₖ' : V → U → Prop) (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) : Prop :=
  IsMarkedCycleTuple (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
    (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b W.1.val ∧
      MarkedHubCompatible H₀' Hₖ' W.1.val W.2.val

def markedWheelRestrictionEquiv (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u) :
    {W : MarkedWheel tail head ktail khead m π b H₀ Hₖ // MarkedWheelSurvives PE PK H₀' Hₖ' W} ≃
      MarkedWheel (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ' where
  toFun W := ⟨⟨W.val.1.val,W.property.1⟩,⟨W.val.2.val,W.property.2⟩⟩
  invFun W := ⟨markedWheelToLarger PE PK hH₀ hHₖ W,W.1.property,W.2.property⟩
  left_inv W := by rfl
  right_inv W := by rfl

theorem marked_wheel_restricted_resource_load [Fintype V] [Fintype U]
    (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e : Finset V⊕(V×U)) :
    (∑ W : MarkedWheel (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ',
      if e∈markedWheelPhysicalResources W then w (markedWheelToLarger PE PK hH₀ hHₖ W) else 0)=
    ∑ W : MarkedWheel tail head ktail khead m π b H₀ Hₖ,
      if e∈markedWheelPhysicalResources W ∧ MarkedWheelSurvives PE PK H₀' Hₖ' W then w W else 0 := by
  let f (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :=
    if e∈markedWheelPhysicalResources W ∧ MarkedWheelSurvives PE PK H₀' Hₖ' W then w W else 0
  have he := finite_sum_restrict_of_zero (fun W=>MarkedWheelSurvives PE PK H₀' Hₖ' W) f
    (by intro W hW;simp only [f,hW,and_false,ite_false])
  rw [he]
  have hh := (markedWheelRestrictionEquiv PE PK hH₀ hHₖ).sum_comp
    (fun W=>if e∈markedWheelPhysicalResources W then w (markedWheelToLarger PE PK hH₀ hHₖ W) else 0)
  rw [← hh]
  apply Finset.sum_congr rfl
  intro W _
  have hw : markedWheelToLarger PE PK hH₀ hHₖ ((markedWheelRestrictionEquiv PE PK hH₀ hHₖ) W)=W.val := rfl
  have hr : markedWheelPhysicalResources ((markedWheelRestrictionEquiv PE PK hH₀ hHₖ) W)=markedWheelPhysicalResources W.val := by
    rw [← markedWheelToLarger_resources PE PK hH₀ hHₖ,hw]
  rw [hw,hr]
  dsimp only [f]
  simp only [W.property,and_true]



theorem markedRestrictedPhysical_injective (PE : E → Prop) (PK : K → Prop)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π)) :
    Function.Injective (markedPhysicalEdge (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π) := by
  let f : {e // PE e}⊕{e // PK e} → E⊕K := Sum.map Subtype.val Subtype.val
  have hf : Function.Injective f := Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩
  have hphys (e : {e // PE e}⊕{e // PK e}) :
      markedPhysicalEdge (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π e=
          markedPhysicalEdge tail head ktail khead π (f e) := by cases e <;> rfl
  intro e f he
  exact hf (hp (by simpa only [hphys] using he))

theorem markedWheelToLarger_injective (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π)) :
    Function.Injective (markedWheelToLarger (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (π:=π) (m:=m) (b:=b) PE PK hH₀ hHₖ) := by
  intro W Z he
  apply markedWheelPhysicalResources_injective (markedRestrictedPhysical_injective PE PK hp)
  have hh := congrArg (fun T : MarkedWheel tail head ktail khead m π b H₀ Hₖ=>markedWheelPhysicalResources T) he
  simpa only [markedWheelToLarger_resources] using hh



theorem markedWheelToLarger_cover (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (M : Finset (MarkedWheel (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ')) :
    (M.image (markedWheelToLarger PE PK hH₀ hHₖ)).biUnion markedWheelPhysicalResources=
      M.biUnion markedWheelPhysicalResources := by
  rw [Finset.image_biUnion]
  simp only [markedWheelToLarger_resources]

theorem markedWheelToLarger_matching (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (M : Finset (MarkedWheel (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ'))
    (hM : ∀ W∈M,∀ Z∈M,W≠Z → Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) :
    ∀ W∈M.image (markedWheelToLarger PE PK hH₀ hHₖ),
      ∀ Z∈M.image (markedWheelToLarger PE PK hH₀ hHₖ),W≠Z →
        Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z) := by
  intro W hW Z hZ hne
  obtain ⟨W',hW',rfl⟩ := Finset.mem_image.mp hW
  obtain ⟨Z',hZ',rfl⟩ := Finset.mem_image.mp hZ
  simp only [markedWheelToLarger_resources]
  exact hM W' hW' Z' hZ' (fun he=>hne (congrArg (markedWheelToLarger PE PK hH₀ hHₖ) he))

end Oberwolfach
