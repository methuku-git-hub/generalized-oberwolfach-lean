module

public import Oberwolfach.ResourceRootEmbedding

@[expose] public section
/-! An injective resource embedding preserves each fixed weighted pair
sum exactly, including the root-omission condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B I:Type} [Fintype A] [Fintype B] [Fintype I] [DecidableEq A] [DecidableEq B]

theorem resource_omitted_pair_weight_map_outside_right
    (R:I→Finset A) (w:I→ℝ) (f:A↪B) (e g:B) (hg:∀a,f a≠g):
    resourceOmittedPairWeight (fun i=>(R i).map f) w e g=0 :=by
  unfold resourceOmittedPairWeight
  apply Finset.sum_eq_zero
  intro i _
  have hm:g∉(R i).map f:=by
    intro h
    obtain ⟨a,_,ha⟩:=Finset.mem_map.mp h
    exact hg a ha
  simp [hm]
end Oberwolfach
