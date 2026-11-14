module

public import Oberwolfach.MarkedDirectedWheelInterval

@[expose] public section
/-! The terminal interval label avoids all selected rim vertices when ordinary
spokes avoid that label and the extended interval has distinct labels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_run_terminal_avoids_rim_supports
    {V:Type*} (v:ℕ → V) (c n start:ℕ) (hc:0 < c) (C:ℕ → Fin c → V)
    (Ord:V → Prop)
    (hroot:∀ i,start ≤ i → i < start+n → C i ⟨0,hc⟩=v i)
    (hlabels:∀ i,start ≤ i → i < start+n → v (start+n)≠v i)
    (hordinary:∀ i,start ≤ i → i < start+n → ∀ a:Fin c,a.val ≠ 0 → Ord (C i a))
    (havoid:¬Ord (v (start+n))):
    ∀ i,start ≤ i → i < start+n → ∀ a:Fin c,v (start+n)≠C i a:=by
  intro i hi hj a heq
  by_cases ha:a.val=0
  · have ha':a=⟨0,hc⟩:=Fin.ext ha
    subst a
    exact hlabels i hi hj (heq.trans (hroot i hi hj))
  · apply havoid
    rw [heq]
    exact hordinary i hi hj a ha
end Oberwolfach
