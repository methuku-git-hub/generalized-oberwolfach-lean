module

public import Oberwolfach.SignedDemandNormalization

@[expose] public section
/-! Occurrence degrees are invariant under simultaneous relabelling of
occurrences and endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem occurrence_degree_equiv_relabel
    {V W E F:Type} [Fintype E] [Fintype F] [DecidableEq V] [DecidableEq W]
    (v:V≃W) (e:E≃F) (tail:E→V) (tail':F→W)
    (h:∀a,tail' (e a)=v (tail a)) (x:V):
    occurrenceDegree tail x=occurrenceDegree tail' (v x):=by
  unfold occurrenceDegree
  apply Fintype.sum_equiv e
  intro a
  rw [h]
  simp only [Equiv.apply_eq_iff_eq]
  split_ifs <;> rfl
end Oberwolfach
