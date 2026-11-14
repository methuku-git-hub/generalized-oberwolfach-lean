module

public import Oberwolfach.MarkedActiveSubhostIncidence
public import Oberwolfach.MarkedDeletedSampleResources

@[expose] public section

/-! Incidence bounds on any further removed resources transfer exactly
from a physically deleted sample to its original fixed reference host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_full_resources_active_image
    {V U E K : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V) (H₀ HK : V→U→Prop) :
    markedFiniteResources tail head ktail khead π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2))=
      Finset.univ.image (markedActivePhysical tail head ktail khead π H₀ HK) := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨Sum.inl a,Finset.mem_univ _,ha⟩
    · obtain ⟨vu,hvu,hz⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨Sum.inr ⟨vu,(Finset.mem_filter.mp hvu).2⟩,Finset.mem_univ _,hz⟩
  · intro hz
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hz
    cases e with
    | inl a => exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
    | inr vu => exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨vu.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,vu.property⟩,rfl⟩)

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_deleted_host_incidence_card
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) (DR : SimpleGraph V) (DS : SimpleGraph (V⊕U)) :
    let σ' := rawMarkedDeleteRims σ DR.edgeFinset
    let H' := markedDeletePhysicalSpokes H DS
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let E' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    ∀ B : Finset (Finset V⊕(V×U)),
    B⊆markedFiniteResources (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2))→
    ∀ physical x,
    ((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        π (H false) (H true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        π (H false) (H true) e∈B)).card=
    ((markedIncidentEdges (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
        π (H' false) (H' true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
        π (H' false) (H' true) e∈B)).card := by
  intro σ' H' E K E' K' B hB physical x
  let f : E'↪E := (markedSampleDeletedArcEquiv P π d σ DR.edgeFinset false).toEmbedding.trans
    (Function.Embedding.subtype _)
  let g : K'↪K := (markedSampleDeletedArcEquiv P π d σ DR.edgeFinset true).toEmbedding.trans
    (Function.Embedding.subtype _)
  apply markedActiveSubhostEmbedding_incidence_card
    (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
    (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
    π f g (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    (H false) (H true) (H' false) (H' true) (fun _ _ h=>h.1) (fun _ _ h=>h.1)
    (markedSampleArc_physical_injective P π (3*d) _)
  rw [←marked_full_resources_active_image]
  exact hB

end Oberwolfach
