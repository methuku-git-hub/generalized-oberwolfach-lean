module

public import Oberwolfach.OrdinaryInducedRawResource

@[expose] public section
/-! An induced-domain wheel reads disjoint ambient primitive coordinates
on its distinct resources when the ambient conflict graph is forbidden. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_raw_candidate_disjoint
    (P F : SimpleGraph V) (A : Set V) (u : U) (π : Equiv.Perm V) (d r : ℕ)
    (hF : permutationConflictGraph π (3*d) ≤ F)
    (W : OrdinaryWheel (P.induce A) (F.induce A) (fun _ : A => fun _ : Unit => True) r)
    (a b : Sym2 A ⊕ (A × Unit))
    (ha : a ∈ ordinaryWheelResources W) (hb : b ∈ ordinaryWheelResources W) (hne : a ≠ b) :
    Disjoint (ordinaryInducedRawCoordinates A u π d a) (ordinaryInducedRawCoordinates A u π d b) := by
  apply rawWheelResourceCoordinates_disjoint π d _ _
    (fun he => hne (ordinary_induced_raw_resource_injective A u he))
  intro v t w z hav hbw
  cases a with
  | inl a => simp [ordinaryInducedRawResource] at hav
  | inr a =>
    cases b with
    | inl b => simp [ordinaryInducedRawResource] at hbw
    | inr b =>
      have ha' := (ordinaryWheelResources_spoke W a.1 a.2).mp ha
      have hb' := (ordinaryWheelResources_spoke W b.1 b.2).mp hb
      have heqa : a.1.val = v ∧ u = t := by
        simpa only [ordinaryInducedRawResource, Sum.inr.injEq, Prod.mk.injEq] using hav
      have heqb : b.1.val = w ∧ u = z := by
        simpa only [ordinaryInducedRawResource, Sum.inr.injEq, Prod.mk.injEq] using hbw
      have hab : a.1 ≠ b.1 := by
        intro hh
        apply hne
        apply congrArg Sum.inr
        exact Prod.ext hh (Subsingleton.elim _ _)
      right
      intro hc
      have hclose : PermutationClose π (3*d) a.1.val b.1.val := by
        simpa only [heqa.1, heqb.1] using hc
      have hne' : a.1.val ≠ b.1.val := fun h => hab (Subtype.val_injective h)
      exact W.property.2 a.1 ha'.2 b.1 hb'.2 (hF ⟨hne',hclose⟩)
end Oberwolfach
