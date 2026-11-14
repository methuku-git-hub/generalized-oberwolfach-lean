module

public import Oberwolfach.MarkedSpokeReplacement

@[expose] public section

/-! Two actual marked cycles that differ only at one specified position,
with both cycles compatible with both specified hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev MarkedReplacementPair {V U E K : Type*}
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (H₀ Hₖ : V → U → Prop) (i : Fin (m+1)) (v v' : V) (u u' : U) :=
  {P : MarkedCycleTuple tail head ktail khead m π b × MarkedCycleTuple tail head ktail khead m π b //
    P.1.val i=v ∧ P.2.val i=v' ∧ (∀ k,k≠i → P.1.val k=P.2.val k) ∧
    MarkedHubCompatible H₀ Hₖ P.1.val u ∧ MarkedHubCompatible H₀ Hₖ P.1.val u' ∧
    MarkedHubCompatible H₀ Hₖ P.2.val u ∧ MarkedHubCompatible H₀ Hₖ P.2.val u'}

variable {V U E K : Type*}
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} {i : Fin (m+1)} {v v' : V} {u u' : U}

theorem markedReplacementPair_left_injective : Function.Injective
    (fun P : MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u'=>P.val.1) := by
  intro P Q h
  change P.val.1=Q.val.1 at h
  apply Subtype.ext
  apply Prod.ext h
  apply Subtype.ext
  funext k
  by_cases hk : k=i
  · subst k;exact P.property.2.1.trans Q.property.2.1.symm
  · rw [← P.property.2.2.1 k hk,← Q.property.2.2.1 k hk,h]

theorem markedReplacementPair_right_injective : Function.Injective
    (fun P : MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u'=>P.val.2) := by
  intro P Q h
  change P.val.2=Q.val.2 at h
  apply Subtype.ext
  apply Prod.ext _ h
  apply Subtype.ext
  funext k
  by_cases hk : k=i
  · subst k;exact P.property.1.trans Q.property.1.symm
  · rw [P.property.2.2.1 k hk,Q.property.2.2.1 k hk,h]

def markedReplacementWheel (a d : Bool) :
    MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u' ↪
      MarkedWheel tail head ktail khead m π b H₀ Hₖ where
  toFun P := ⟨if a then P.val.2 else P.val.1,⟨if d then u' else u,by
    cases a <;> cases d
    · exact P.property.2.2.2.1
    · exact P.property.2.2.2.2.1
    · exact P.property.2.2.2.2.2.1
    · exact P.property.2.2.2.2.2.2⟩⟩
  inj' P Q he := by
    have hc := congrArg Sigma.fst he
    cases a
    · exact markedReplacementPair_left_injective hc
    · exact markedReplacementPair_right_injective hc

end Oberwolfach
