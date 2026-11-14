module

public import Oberwolfach.MatchingPhysicalLift

@[expose] public section
/-! A hub-preserving injective realization preserves every selected hub count. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem realization_hub_count {C W U:Type} [DecidableEq C] [DecidableEq W] [DecidableEq U]
    (S:Finset C) (lift:C→W) (hubC:C→U) (hubW:W→U)
    (hinj:Set.InjOn lift (↑S:Set C)) (hhub:∀c∈S,hubW (lift c)=hubC c) (u:U):
    ((S.image lift).filter (fun W=>hubW W=u)).card =
      (S.filter (fun c=>hubC c=u)).card :=by
  have hset:(S.image lift).filter (fun W=>hubW W=u)=
      (S.filter (fun c=>hubC c=u)).image lift :=by
    ext W
    simp only [Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨⟨c,hc,rfl⟩,hW⟩
      exact ⟨c,⟨hc,(hhub c hc).symm.trans hW⟩,rfl⟩
    · rintro ⟨c,⟨hc,hu⟩,rfl⟩
      exact ⟨⟨c,hc,rfl⟩,(hhub c hc).trans hu⟩
  rw [hset]
  apply Finset.card_image_of_injOn
  intro c hc d hd hcd
  exact hinj (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hd).1 hcd
end Oberwolfach
