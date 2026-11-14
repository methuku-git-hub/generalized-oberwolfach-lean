module

public import Mathlib.Data.Finset.Basic

@[expose] public section
/-! Restricting to unmarked candidates at one hub and then to a cycle
index gives the same set as the original matching's hub-index test. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selected_hub_filter {A I U:Type} [DecidableEq A] [DecidableEq I] [DecidableEq U]
    (L:Finset A) (tag:A→Option I) (hub:A→U) (i₀ i:I) (u:U):
    (L.filter (fun a=>(tag a).isSome ∧ hub a=u)).filter (fun a=>(tag a).getD i₀=i)=
      L.filter (fun a=>tag a=some i ∧ hub a=u):=by
  ext a
  simp only [Finset.mem_filter]
  cases h:tag a with
  | none => simp [h]
  | some j => simp [h, and_assoc, and_left_comm, and_comm]
end Oberwolfach
