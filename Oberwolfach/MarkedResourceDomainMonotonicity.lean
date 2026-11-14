module

public import Oberwolfach.MarkedProtectedResourceRestoration

@[expose] public section

/-! Nested row and hub domains induce nested physical stars and inner
resource sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V U : Type} [DecidableEq V] [DecidableEq U]

theorem markedStarResource_mono {I T : Finset V} {J Q : Finset U}
    (hT : T⊆I) (hQ : Q⊆J) (e : Finset V⊕(V×U)) :
    markedStarResource T Q e→markedStarResource I J e := by
  cases e with
  | inl e => rintro ⟨x,hx,hT'⟩;exact ⟨x,hx,hT hT'⟩
  | inr s => exact Or.imp (fun h=>hT h) (fun h=>hQ h)

theorem markedInnerResource_mono {I T : Finset V} {J Q : Finset U}
    (hT : T⊆I) (hQ : Q⊆J) (e : Finset V⊕(V×U)) :
    markedInnerResource T Q e→markedInnerResource I J e := by
  cases e with
  | inl e => exact fun h=>h.trans hT
  | inr s => exact And.imp (fun h=>hT h) (fun h=>hQ h)

end Oberwolfach
