module

public import Oberwolfach.OrdinaryPhysicalCommonDomains

@[expose] public section
/-! Every finite set contained in one side of a sum is the image of its
unique original-domain trace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_left_subset_image (S:Finset (V⊕U))
    (h:S⊆Finset.univ.image (Sum.inl:V→V⊕U)):
    ∃T:Finset V,T.image Sum.inl=S ∧ T.card=S.card:=by
  let T:Finset V:=Finset.univ.filter (fun v=>Sum.inl v∈S)
  have he:T.image (Sum.inl:V→V⊕U)=S:=by
    ext z
    cases z with
    | inl v=>simp [T]
    | inr u=>
      have hu:Sum.inr u∉S:=by
        intro hu
        have := h hu
        simpa using this
      simp [hu]
  refine ⟨T,he,?_⟩
  have hc:=Finset.card_image_of_injective T (Sum.inl_injective:Function.Injective (Sum.inl:V→V⊕U))
  rw [he] at hc
  exact hc.symm

theorem ordinary_physical_right_subset_image (S:Finset (V⊕U))
    (h:S⊆Finset.univ.image (Sum.inr:U→V⊕U)):
    ∃T:Finset U,T.image Sum.inr=S ∧ T.card=S.card:=by
  let T:Finset U:=Finset.univ.filter (fun u=>Sum.inr u∈S)
  have he:T.image (Sum.inr:U→V⊕U)=S:=by
    ext z
    cases z with
    | inl v=>
      have hv:Sum.inl v∉S:=by
        intro hv
        have := h hv
        simpa using this
      simp [hv]
    | inr u=>simp [T]
  refine ⟨T,he,?_⟩
  have hc:=Finset.card_image_of_injective T (Sum.inr_injective:Function.Injective (Sum.inr:U→V⊕U))
  rw [he] at hc
  exact hc.symm
end Oberwolfach
