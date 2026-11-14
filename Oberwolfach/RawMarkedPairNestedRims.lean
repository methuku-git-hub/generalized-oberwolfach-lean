module

public import Oberwolfach.RawMarkedRestrictionComposition

@[expose] public section
/-! Two successive restrictions read the same original physical rim edges
as their composite, independently of either hub map. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V A W U Z T Γ Color:Type} [Fintype V] [Fintype A] [Fintype W]
  [Fintype U] [Fintype Z] [Fintype T] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder A] [LinearOrder W]
  [DecidableEq U] [DecidableEq Z] [DecidableEq T]

theorem rawMarked_pair_nested_rims (f:A→V) (i:W→A) (g:Z→U) (j:T→Z)
    (σ:RawMarkedOutcome V U Γ Color) (e:Sym2 W):
    rawMarkedRestrictPair i j (rawMarkedRestrictPair f g σ) (Sum.inl e)=
      rawMarkedRestrictPair (f∘i) (g∘j) σ (Sum.inl e):=by
  change σ (Sum.inl (Sym2.map f (Sym2.map i e)))=σ (Sum.inl (Sym2.map (f∘i) e))
  rw [Sym2.map_map]
end Oberwolfach
