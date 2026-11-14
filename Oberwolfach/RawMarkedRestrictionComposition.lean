module

public import Oberwolfach.RawMarkedPairRestriction

@[expose] public section

/-! Nested restrictions read the same original coordinates. These are
pointwise identities, before any event or later deletion is chosen. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V A W U Z Γ Color:Type} [Fintype V] [Fintype A] [Fintype W]
  [Fintype U] [Fintype Z] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder A] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem rawMarkedRestrictVertices_pair_comp (f:A→V) (i:W→A) (g:Z→U)
    (σ:RawMarkedOutcome V U Γ Color):
    rawMarkedRestrictVertices i (rawMarkedRestrictPair f g σ)=rawMarkedRestrictPair (f∘i) g σ:=by
  funext e
  cases e with
  | inl e=>
    change σ (Sum.inl (Sym2.map f (Sym2.map i e)))=σ (Sum.inl (Sym2.map (f∘i) e))
    rw [Sym2.map_map]
  | inr z=>
    obtain ⟨z,j⟩:=z
    cases j with
    | inl x=>rfl
    | inr j=>cases j <;> rfl

end Oberwolfach
