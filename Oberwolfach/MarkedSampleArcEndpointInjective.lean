module

public import Oberwolfach.MarkedSampleArcs

@[expose] public section
/-! Sample arcs are subtypes of ordered endpoint pairs, so their endpoint
maps are injective without any additional host assumption. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem marked_sample_arc_endpoint_injective (P:SimpleGraph V) (π:Equiv.Perm V)
    (b:ℕ) (σ:Sym2 V→Option (Bool×Bool)) (mark:Bool) :
    Function.Injective (fun e:MarkedSampleArc P π b σ mark => (e.val.1,e.val.2)) := by
  intro e e' h
  apply Subtype.ext
  exact h
end Oberwolfach
