module

public import Oberwolfach.OrdinaryEmptyRootCover

@[expose] public section
/-! A root cover needed only on a good event can be chosen as a total
outcome-dependent family by taking empty roots and an empty cover off it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Ω:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_guarded_root_cover_selection
    (Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop)
    (X T:Ω→Finset V) (Z W:Ω→Finset U) (r:ℕ) (η ell:ℝ) (hη:0≤η) (hell:0≤ell)
    (E:Ω→Prop)
    (hcover:∀s,E s→Nonempty (OrdinaryRootCoverNonrootData (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r η ell)):
    ∃(T' : Ω→Finset V) (W' : Ω→Finset U),
      (∀s,E s→T' s=T s ∧ W' s=W s) ∧
      Nonempty (∀s,OrdinaryRootCoverNonrootData (Q s) (F s) (H s) (X s) (T' s) (Z s) (W' s) r η ell):=by
  let T':Ω→Finset V:=fun s=>if E s then T s else ∅
  let W':Ω→Finset U:=fun s=>if E s then W s else ∅
  refine ⟨T',W',?_,?_⟩
  · intro s hs
    simp [T',W',hs]
  · refine ⟨fun s=>?_⟩
    by_cases hs:E s
    · simpa [T',W',hs] using Classical.choice (hcover s hs)
    · simpa [T',W',hs] using Classical.choice (ordinary_empty_root_cover (Q s) (F s) (H s) (X s) (Z s) r η ell hη hell)
end Oberwolfach
