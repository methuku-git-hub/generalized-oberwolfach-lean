module

public import Oberwolfach.OrdinaryRootStarBoundaryZero

@[expose] public section
/-! Avoidance of a larger root star is preserved for any nested root pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_root_star_mono (T Tplus:Finset V) (W Wplus:Finset U)
    (hT:T⊆Tplus) (hW:W⊆Wplus):ordinaryDeepRootStar T W≤ordinaryDeepRootStar Tplus Wplus:=by
  intro a b hab
  cases a with
  | inl v=>cases b with
    | inl w=>
      exact ⟨hab.1,hab.2.elim (fun h=>Or.inl (hT h)) (fun h=>Or.inr (hT h))⟩
    | inr u=>exact ⟨trivial,hab.2.elim (fun h=>Or.inl (hT h)) (fun h=>Or.inr (hW h))⟩
  | inr u=>cases b with
    | inl v=>exact ⟨trivial,hab.2.elim (fun h=>Or.inl (hT h)) (fun h=>Or.inr (hW h))⟩
    | inr z=>exact hab.elim
end Oberwolfach
