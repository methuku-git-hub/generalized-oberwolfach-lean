module

public import Oberwolfach.MarkedIncidentResources

@[expose] public section

/-! Deleting edges preserves both physical and auxiliary incidences of
every surviving resource. In particular, incidence bounds for a further
deletion are identical in the remaining host and the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K' : Type*} [Fintype V] [Fintype U]
    [Fintype E] [Fintype K] [Fintype E'] [Fintype K']
    [DecidableEq V] [DecidableEq U]

def markedActiveSubhostEmbedding (f : E'↪E) (g : K'↪K)
    (H₀ Hₖ H₀' Hₖ' : V→U→Prop)
    (h₀ : ∀ v u,H₀' v u→H₀ v u) (hₖ : ∀ v u,Hₖ' v u→Hₖ v u) :
    MarkedActiveEdge E' K' H₀' Hₖ'↪MarkedActiveEdge E K H₀ Hₖ :=
  (f.sumMap g).sumMap
    ⟨fun vu=>⟨vu.val,vu.property.elim (fun h=>Or.inl (h₀ _ _ h))
      (fun h=>Or.inr (hₖ _ _ h))⟩,fun a b h=>Subtype.ext (congrArg (fun vu : {vu : V×U // H₀ vu.1 vu.2 ∨ Hₖ vu.1 vu.2}=>vu.val) h)⟩

theorem markedActiveSubhostEmbedding_physical
    (tail head : E→V) (ktail khead : K→V) (tail' head' : E'→V) (ktail' khead' : K'→V)
    (π : Equiv.Perm V) (f : E'↪E) (g : K'↪K)
    (ht : ∀ e,tail (f e)=tail' e) (hh : ∀ e,head (f e)=head' e)
    (hkt : ∀ e,ktail (g e)=ktail' e) (hkh : ∀ e,khead (g e)=khead' e)
    (H₀ Hₖ H₀' Hₖ' : V→U→Prop)
    (h₀ : ∀ v u,H₀' v u→H₀ v u) (hₖ : ∀ v u,Hₖ' v u→Hₖ v u)
    (e : MarkedActiveEdge E' K' H₀' Hₖ') :
    markedActivePhysical tail head ktail khead π H₀ Hₖ
        (markedActiveSubhostEmbedding f g H₀ Hₖ H₀' Hₖ' h₀ hₖ e)=
      markedActivePhysical tail' head' ktail' khead' π H₀' Hₖ' e := by
  cases e with
  | inl e => cases e <;> simp [markedActiveSubhostEmbedding,markedActivePhysical,markedPhysicalEdge,ht,hh,hkt,hkh]
  | inr vu => rfl

theorem markedActiveSubhostEmbedding_incident
    (tail head : E→V) (ktail khead : K→V) (tail' head' : E'→V) (ktail' khead' : K'→V)
    (π : Equiv.Perm V) (f : E'↪E) (g : K'↪K)
    (ht : ∀ e,tail (f e)=tail' e) (hh : ∀ e,head (f e)=head' e)
    (hkt : ∀ e,ktail (g e)=ktail' e) (hkh : ∀ e,khead (g e)=khead' e)
    (H₀ Hₖ H₀' Hₖ' : V→U→Prop)
    (h₀ : ∀ v u,H₀' v u→H₀ v u) (hₖ : ∀ v u,Hₖ' v u→Hₖ v u)
    (physical : Bool) (x : V⊕U) (e : MarkedActiveEdge E' K' H₀' Hₖ') :
    markedResourceIncident tail head ktail khead π H₀ Hₖ physical x
        (markedActiveSubhostEmbedding f g H₀ Hₖ H₀' Hₖ' h₀ hₖ e) ↔
      markedResourceIncident tail' head' ktail' khead' π H₀' Hₖ' physical x e := by
  cases x <;> cases e with
  | inl e => cases e <;> simp [markedActiveSubhostEmbedding,markedResourceIncident,ht,hh,hkt,hkh]
  | inr vu => rfl

theorem markedActiveSubhostEmbedding_incidence_card
    (tail head : E→V) (ktail khead : K→V) (tail' head' : E'→V) (ktail' khead' : K'→V)
    (π : Equiv.Perm V) (f : E'↪E) (g : K'↪K)
    (ht : ∀ e,tail (f e)=tail' e) (hh : ∀ e,head (f e)=head' e)
    (hkt : ∀ e,ktail (g e)=ktail' e) (hkh : ∀ e,khead (g e)=khead' e)
    (H₀ Hₖ H₀' Hₖ' : V→U→Prop)
    (h₀ : ∀ v u,H₀' v u→H₀ v u) (hₖ : ∀ v u,Hₖ' v u→Hₖ v u)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (B : Finset (Finset V⊕(V×U)))
    (hB : B⊆Finset.univ.image (markedActivePhysical tail' head' ktail' khead' π H₀' Hₖ'))
    (physical : Bool) (x : V⊕U) :
    ((markedIncidentEdges tail head ktail khead π H₀ Hₖ physical x).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ Hₖ e∈B)).card=
    ((markedIncidentEdges tail' head' ktail' khead' π H₀' Hₖ' physical x).filter
      (fun e=>markedActivePhysical tail' head' ktail' khead' π H₀' Hₖ' e∈B)).card := by
  let F := markedActiveSubhostEmbedding f g H₀ Hₖ H₀' Hₖ' h₀ hₖ
  have hphys := markedActiveSubhostEmbedding_physical tail head ktail khead tail' head' ktail' khead'
    π f g ht hh hkt hkh H₀ Hₖ H₀' Hₖ' h₀ hₖ
  have hinc := markedActiveSubhostEmbedding_incident tail head ktail khead tail' head' ktail' khead'
    π f g ht hh hkt hkh H₀ Hₖ H₀' Hₖ' h₀ hₖ physical x
  have he : (((markedIncidentEdges tail' head' ktail' khead' π H₀' Hₖ' physical x).filter
      (fun e=>markedActivePhysical tail' head' ktail' khead' π H₀' Hₖ' e∈B)).image F)=
      ((markedIncidentEdges tail head ktail khead π H₀ Hₖ physical x).filter
      (fun e=>markedActivePhysical tail head ktail khead π H₀ Hₖ e∈B)) := by
    ext e
    constructor
    · intro he
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨ha,hbe⟩ := Finset.mem_filter.mp ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · exact (hinc a).mpr (Finset.mem_filter.mp ha).2
      · change markedActivePhysical tail head ktail khead π H₀ Hₖ (F a)∈B
        rw [hphys]
        exact hbe
    · intro he
      obtain ⟨he,hbe⟩ := Finset.mem_filter.mp he
      obtain ⟨e',_,he'⟩ := Finset.mem_image.mp (hB hbe)
      have hfe : F e'=e := (markedActivePhysical_injective hp) ((hphys e').trans he')
      refine Finset.mem_image.mpr ⟨e',Finset.mem_filter.mpr ⟨?_,?_⟩,hfe⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,(hinc e').mp ?_⟩
        change markedResourceIncident tail head ktail khead π H₀ Hₖ physical x (F e')
        rw [hfe]
        exact (Finset.mem_filter.mp he).2
      · rw [he']
        exact hbe
  rw [←he,Finset.card_image_of_injective _ F.injective]

end Oberwolfach
