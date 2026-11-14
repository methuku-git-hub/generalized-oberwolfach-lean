module

public import Oberwolfach.EdgeAssignmentAvailableIndex

@[expose] public section
/-! An option-valued assignment that is defined on every edge in a finite
set gives a genuine function on the subtype of those edges, preserving each
index's exact load. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W:Type} [Fintype E] [DecidableEq E] [DecidableEq W]

theorem edge_assignment_option_to_function (S:Finset E) (f:E→Option W)
    (hfull:∀e∈S,∃w,f e=some w):
    ∃g:{e:E // e∈S}→W,
      (∀e,f e.1=some (g e)) ∧
      (∀w,(Finset.univ.filter (fun e:{e:E // e∈S}=>g e=w)).card=
        (S.filter (fun e=>f e=some w)).card) := by
  let g:{e:E // e∈S}→W:=fun e=>Classical.choose (hfull e.1 e.2)
  have hg:∀e,f e.1=some (g e):=fun e=>Classical.choose_spec (hfull e.1 e.2)
  refine ⟨g,hg,?_⟩
  intro w
  apply Finset.card_bij (fun e _=>e.1)
  · intro e he
    have he':g e=w:=(Finset.mem_filter.mp he).2
    apply Finset.mem_filter.mpr
    exact ⟨e.2,by rw [hg e,he']⟩
  · intro a ha b hb hab
    exact Subtype.ext hab
  · intro e he
    have hh:=Finset.mem_filter.mp he
    let x:{e:E // e∈S}:=⟨e,hh.1⟩
    have hx:g x=w:=Option.some.inj ((hg x).symm.trans hh.2)
    refine ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ x,hx⟩,rfl⟩
end Oberwolfach
