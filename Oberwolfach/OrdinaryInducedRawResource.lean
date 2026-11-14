module

public import Oberwolfach.OrdinaryRawIntervalGeometry

@[expose] public section

/-! Restricting wheel resources to an induced inner vertex set keeps their
original primitive coordinates; the permutation remains on the full space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def ordinaryInducedRawResource (A : Set V) (u : U) : Sym2 A ⊕ (A × Unit) → Sym2 V ⊕ (V × U)
  | Sum.inl e => Sum.inl (Sym2.map Subtype.val e)
  | Sum.inr a => Sum.inr (a.1.val, u)

theorem ordinary_induced_raw_resource_injective (A : Set V) (u : U) :
    Function.Injective (ordinaryInducedRawResource A u) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hb : Sym2.map Subtype.val a = Sym2.map Subtype.val b := Sum.inl.inj h
      exact congrArg Sum.inl (Sym2.map.injective Subtype.val_injective hb)
    | inr b => cases h
  | inr a =>
    cases b with
    | inl b => cases h
    | inr b =>
      have hv : a.1.val = b.1.val := congrArg Prod.fst (Sum.inr.inj h)
      have hfirst : a.1 = b.1 := Subtype.val_injective hv
      cases a with
      | mk av au =>
        cases b with
        | mk bv bu =>
          cases au
          cases bu
          simp only at hfirst
          subst bv
          rfl

def ordinaryInducedRawCoordinates (A : Set V) (u : U) (π : Equiv.Perm V) (d : ℕ)
    (a : Sym2 A ⊕ (A × Unit)) : Finset (RawWheelCoordinate V U) :=
  rawWheelResourceCoordinates π d (ordinaryInducedRawResource A u a)

theorem ordinary_induced_raw_coordinates_card (A : Set V) (u : U) (π : Equiv.Perm V) (d : ℕ)
    (a : Sym2 A ⊕ (A × Unit)) :
    (ordinaryInducedRawCoordinates A u π d a).card ≤ 4*d+3 :=
  rawWheelResourceCoordinates_card π d _

theorem ordinary_induced_raw_coordinates_reverse_card (A : Set V) (u : U)
    (π : Equiv.Perm V) (d : ℕ) (e : RawWheelCoordinate V U) :
    (Finset.univ.filter (fun a : Sym2 A ⊕ (A × Unit) =>
      e ∈ ordinaryInducedRawCoordinates A u π d a)).card ≤ 4*d+3 := by
  apply (Finset.card_le_card_of_injOn (ordinaryInducedRawResource A u) ?_ ?_).trans
    (rawWheelResourceCoordinates_reverse_card π d e)
  · intro a ha
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact ordinary_induced_raw_resource_injective A u hab

theorem ordinary_induced_raw_state_supported (P : SimpleGraph V) (A : Set V) (u : U)
    (π : Equiv.Perm V) (d : ℕ) (j : Color)
    (a : Sym2 A ⊕ (A × Unit)) (σ τ : RawWheelOutcome V U Γ Color)
    (ha : ∀ e ∈ ordinaryInducedRawCoordinates A u π d a, σ e = τ e) :
    ordinaryResourceState ((rawWheelGraph P σ).induce A)
        (fun x (_ : Unit) => rawWheelSpokes π d σ j x.val u) a =
      ordinaryResourceState ((rawWheelGraph P τ).induce A)
        (fun x (_ : Unit) => rawWheelSpokes π d τ j x.val u) a := by
  have hh := rawWheelResourceState_supported P π d j (ordinaryInducedRawResource A u a) σ τ ha
  cases a with
  | inl a =>
    induction a using Sym2.ind with
    | _ x y =>
      have hm : Sym2.map Subtype.val s(x,y) = s(x.val,y.val) := rfl
      change ordinaryResourceState (rawWheelGraph P σ) (rawWheelSpokes π d σ j)
        (Sum.inl (Sym2.map Subtype.val s(x,y))) =
        ordinaryResourceState (rawWheelGraph P τ) (rawWheelSpokes π d τ j)
          (Sum.inl (Sym2.map Subtype.val s(x,y))) at hh
      simp only [hm] at hh
      simpa only [ordinaryInducedRawResource, ordinaryResourceState,
        Sum.elim_inl, SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj] using hh
  | inr a =>
    simpa only [ordinaryInducedRawResource, ordinaryResourceState, Sum.elim_inr] using hh
end Oberwolfach
