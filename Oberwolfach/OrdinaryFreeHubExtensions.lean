module

public import Oberwolfach.OrdinaryDeepFreeExtensions

@[expose] public section
/-! Removing protected hubs loses at most their number from a common-hub
extension count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_free_hub_extension_count (H:V→U→Prop) (Z W:Finset U) (a c:V):
    ((Z.filter (fun u=>H a u∧H c u)).card:ℝ) ≤
      (((Z\W).filter (fun u=>H a u∧H c u)).card:ℝ)+W.card := by
  let S:=Z.filter (fun u=>H a u∧H c u)
  let S':=(Z\W).filter (fun u=>H a u∧H c u)
  have hsub:S\W⊆S' := by
    intro u hu
    have huS:u∈S:=(Finset.mem_sdiff.mp hu).1
    have huW:u∉W:=(Finset.mem_sdiff.mp hu).2
    simp only [S,Finset.mem_filter] at huS
    simp only [S',Finset.mem_filter,Finset.mem_sdiff]
    exact ⟨⟨huS.1,huW⟩,huS.2⟩
  have hc:=Finset.card_sdiff_add_card_inter S W
  have hi:(S∩W).card≤W.card:=Finset.card_le_card Finset.inter_subset_right
  have hs:(S\W).card≤S'.card:=Finset.card_le_card hsub
  have hn:S.card≤S'.card+W.card:=by omega
  exact_mod_cast hn
end Oberwolfach
