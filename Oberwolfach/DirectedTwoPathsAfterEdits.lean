module

public import Oberwolfach.OrientationRouting

@[expose] public section
/-! Directed two-path supply survives bounded physical changes at its two
endpoints. This applies to a class graph of arbitrary density. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem directed_two_paths_after_edits
    {V:Type} [Fintype V] [DecidableEq V] (S:SimpleGraph V)
    (Raw:V→V→Prop) (M:V→V→ℕ) (b:ℝ) (hb:0≤b)
    (hhost:∀x y,0<M x y→S.Adj x y)
    (hchange:∀v,((Finset.univ.filter (fun w=>
      (Raw v w ∧ ¬0<M v w) ∨ (Raw w v ∧ ¬0<M w v))).card:ℝ)≤b):
    ∀x y,(((Finset.univ.filter (fun z=>Raw x z ∧ Raw z y)).card:ℝ)-2*b)≤
      ((Finset.univ.filter (fun z=>0<M x z ∧ 0<M z y ∧ S.Adj x z ∧ S.Adj z y)).card:ℝ):=by
  intro x y
  let R:=Finset.univ.filter (fun z=>Raw x z ∧ Raw z y)
  let T:=Finset.univ.filter (fun z=>0<M x z ∧ 0<M z y ∧ S.Adj x z ∧ S.Adj z y)
  let X:=Finset.univ.filter (fun z=>(Raw x z ∧ ¬0<M x z) ∨ (Raw z x ∧ ¬0<M z x))
  let Y:=Finset.univ.filter (fun z=>(Raw y z ∧ ¬0<M y z) ∨ (Raw z y ∧ ¬0<M z y))
  have hsub:R⊆(T∪X)∪Y:=by
    intro z hz
    have hh:Raw x z ∧ Raw z y:=(Finset.mem_filter.mp hz).2
    by_cases hx:0<M x z
    · by_cases hy:0<M z y
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,hy,hhost _ _ hx,hhost _ _ hy⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr ⟨hh.2,hy⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl ⟨hh.1,hx⟩⟩))
  have hc:R.card≤T.card+X.card+Y.card:=by
    calc
      R.card≤((T∪X)∪Y).card:=Finset.card_le_card hsub
      _≤(T∪X).card+Y.card:=Finset.card_union_le _ _
      _≤T.card+X.card+Y.card:=Nat.add_le_add_right (Finset.card_union_le _ _) _
  have hcR:((R.card:ℕ):ℝ)≤T.card+X.card+Y.card:=by exact_mod_cast hc
  have hx:=hchange x
  have hy:=hchange y
  change (X.card:ℝ)≤b at hx
  change (Y.card:ℝ)≤b at hy
  change (R.card:ℝ)-2*b≤T.card
  linarith
end Oberwolfach
