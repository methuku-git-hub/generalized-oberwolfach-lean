module

public import Oberwolfach.MarkedWheelRestriction
public import Oberwolfach.MarkedIncidentResources
public import Oberwolfach.OrdinaryPackingTransport

@[expose] public section

/-! Transport of a marked packing to its parent host. Original occurrence
identifiers and the permutation are preserved, for both auxiliary and physical
incidence. The extra uncovered edges are precisely those removed from the host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m b : ℕ} {π : Equiv.Perm V}
  {H₀ Hₖ H₀' Hₖ' : V → U → Prop}

def markedActiveToLarger (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u) :
    MarkedActiveEdge {e // PE e} {e // PK e} H₀' Hₖ' → MarkedActiveEdge E K H₀ Hₖ :=
  Sum.map (Sum.map Subtype.val Subtype.val)
    (fun vu=>⟨vu.val,vu.property.elim (fun h=>Or.inl (hH₀ _ _ h)) (fun h=>Or.inr (hHₖ _ _ h))⟩)

theorem markedActiveToLarger_injective (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u) :
    Function.Injective (markedActiveToLarger PE PK hH₀ hHₖ) := by
  apply Sum.map_injective.mpr
  exact ⟨Sum.map_injective.mpr ⟨Subtype.val_injective,Subtype.val_injective⟩,
    fun a b he=>Subtype.ext (congrArg (fun vu : {vu : V×U // H₀ vu.1 vu.2 ∨ Hₖ vu.1 vu.2}=>vu.val) he)⟩

theorem markedActiveToLarger_physical (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (e : MarkedActiveEdge {e // PE e} {e // PK e} H₀' Hₖ') :
    markedActivePhysical tail head ktail khead π H₀ Hₖ (markedActiveToLarger PE PK hH₀ hHₖ e)=
      markedActivePhysical (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' Hₖ' e := by
  cases e with
  | inl e => cases e <;> rfl
  | inr vu => rfl

theorem markedActiveToLarger_incident (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (physical : Bool) (x : V⊕U)
    (e : MarkedActiveEdge {e // PE e} {e // PK e} H₀' Hₖ') :
    markedResourceIncident tail head ktail khead π H₀ Hₖ physical x
      (markedActiveToLarger PE PK hH₀ hHₖ e) ↔
    markedResourceIncident (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' Hₖ' physical x e := by
  cases x <;> cases e with
  | inl e => cases e <;> rfl
  | inr vu => rfl

def markedActiveRetained (PE : E → Prop) (PK : K → Prop)
    (H₀' Hₖ' : V → U → Prop) : MarkedActiveEdge E K H₀ Hₖ → Prop
  | Sum.inl (Sum.inl e) => PE e
  | Sum.inl (Sum.inr e) => PK e
  | Sum.inr vu => H₀' vu.val.1 vu.val.2 ∨ Hₖ' vu.val.1 vu.val.2

theorem markedActiveToLarger_range (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (e : MarkedActiveEdge E K H₀ Hₖ) :
    (∃ f,markedActiveToLarger PE PK hH₀ hHₖ f=e) ↔ markedActiveRetained PE PK H₀' Hₖ' e := by
  constructor
  · rintro ⟨f,rfl⟩
    cases f with
    | inl f => cases f with
      | inl f => exact f.property
      | inr f => exact f.property
    | inr vu => exact vu.property
  · intro he
    cases e with
    | inl e => cases e with
      | inl e => exact ⟨Sum.inl (Sum.inl ⟨e,he⟩),rfl⟩
      | inr e => exact ⟨Sum.inl (Sum.inr ⟨e,he⟩),rfl⟩
    | inr vu => exact ⟨Sum.inr ⟨vu.val,he⟩,rfl⟩

theorem markedActiveResources_toLarger (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W : MarkedWheel (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ') :
    (markedActiveResources W).image (markedActiveToLarger PE PK hH₀ hHₖ)=
      markedActiveResources (markedWheelToLarger PE PK hH₀ hHₖ W) := by
  ext e
  constructor
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    simpa only [markedActiveResources,Finset.mem_filter,Finset.mem_univ,true_and,
      markedActiveToLarger_physical,markedWheelToLarger_resources] using ha
  · intro he
    have he' : markedActivePhysical tail head ktail khead π H₀ Hₖ e∈markedWheelPhysicalResources W := by
      simpa only [markedActiveResources,Finset.mem_filter,Finset.mem_univ,true_and,
        markedWheelToLarger_resources] using he
    rw [← markedActiveResources_image W] at he'
    obtain ⟨a,ha,hpa⟩ := Finset.mem_image.mp he'
    refine Finset.mem_image.mpr ⟨a,ha,?_⟩
    apply markedActivePhysical_injective hp
    rw [markedActiveToLarger_physical]
    exact hpa

theorem markedActive_cover_toLarger (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (M : Finset (MarkedWheel (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ')) :
    (M.biUnion markedActiveResources).image (markedActiveToLarger PE PK hH₀ hHₖ)=
      (M.image (markedWheelToLarger PE PK hH₀ hHₖ)).biUnion markedActiveResources := by
  rw [Finset.biUnion_image,Finset.image_biUnion]
  simp only [markedActiveResources_toLarger PE PK hH₀ hHₖ hp]

theorem markedIncidentEdges_toLarger (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (physical : Bool) (x : V⊕U) :
    (markedIncidentEdges (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' Hₖ' physical x).image
      (markedActiveToLarger PE PK hH₀ hHₖ)=
    (markedIncidentEdges tail head ktail khead π H₀ Hₖ physical x).filter
      (markedActiveRetained PE PK H₀' Hₖ') := by
  ext e
  constructor
  · intro he
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
    refine Finset.mem_filter.mpr ⟨?_,(markedActiveToLarger_range PE PK hH₀ hHₖ _).mp ⟨a,rfl⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact (markedActiveToLarger_incident PE PK hH₀ hHₖ physical x a).mpr (Finset.mem_filter.mp ha).2
  · intro he
    obtain ⟨he,hr⟩ := Finset.mem_filter.mp he
    obtain ⟨a,rfl⟩ := (markedActiveToLarger_range PE PK hH₀ hHₖ e).mpr hr
    refine Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    exact (markedActiveToLarger_incident PE PK hH₀ hHₖ physical x a).mp (Finset.mem_filter.mp he).2

theorem marked_leftover_transport (PE : E → Prop) (PK : K → Prop)
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (M : Finset (MarkedWheel (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ'))
    (physical : Bool) (x : V⊕U) :
    (markedIncidentEdges tail head ktail khead π H₀ Hₖ physical x \
      (M.image (markedWheelToLarger PE PK hH₀ hHₖ)).biUnion markedActiveResources).card≤
    (markedIncidentEdges (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' Hₖ' physical x \
      M.biUnion markedActiveResources).card+
    ((markedIncidentEdges tail head ktail khead π H₀ Hₖ physical x).filter
      (fun e=>¬markedActiveRetained PE PK H₀' Hₖ' e)).card := by
  let S := markedIncidentEdges tail head ktail khead π H₀ Hₖ physical x
  let D := S.filter (fun e=>¬markedActiveRetained PE PK H₀' Hₖ' e)
  let C := (M.image (markedWheelToLarger PE PK hH₀ hHₖ)).biUnion markedActiveResources
  have hSD : S\D=S.filter (markedActiveRetained PE PK H₀' Hₖ') := by
    ext e
    simp only [D,Finset.mem_sdiff,Finset.mem_filter]
    tauto
  have hc := finset_uncovered_le_after_deletion S D C
  rw [hSD,← markedIncidentEdges_toLarger PE PK hH₀ hHₖ physical x] at hc
  have himg := Finset.card_image_of_injective
    (markedIncidentEdges (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' Hₖ' physical x \
      M.biUnion markedActiveResources) (markedActiveToLarger_injective PE PK hH₀ hHₖ)
  rw [Finset.image_sdiff _ _ (markedActiveToLarger_injective PE PK hH₀ hHₖ),
    markedActive_cover_toLarger PE PK hH₀ hHₖ hp] at himg
  change (S\C).card≤_+D.card
  rw [← himg]
  exact hc

end Oberwolfach
