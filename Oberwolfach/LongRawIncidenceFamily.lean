module

public import Oberwolfach.LongRawHubContext
public import Oberwolfach.LongTypedResourceCardinality

@[expose] public section
/-! The auxiliary (untwisted endpoint) and typed spoke incidences for one fixed raw
resource set. The physical rim tests are adjoined separately; this index
bound puts all of them in the same cubic-size matching test family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev LongRawIncidenceIndex (n:ℕ) (U:Type) :=
  Fin n ⊕ (Bool×(Fin n⊕U))

def longRawResourceIncident {n:ℕ} {U:Type}:
    LongRawIncidenceIndex n U → LongRawHubResource n U → Prop
  | .inl x, .inl (.inl (v,w)) => v=x ∨ w=x
  | .inl x, .inl (.inr (v,w)) => v=x ∨ w=x
  | .inl _, .inr _ => False
  | .inr (typ,.inl x), .inr (j,v,_) => typ=j ∧ v=x
  | .inr (typ,.inr u), .inr (j,_,v) => typ=j ∧ v=u
  | .inr _, .inl _ => False

def longRawIncidenceSet {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (S:Finset (LongRawHubResource n U)) (i:LongRawIncidenceIndex n U):Finset S :=
  Finset.univ.filter (fun v=>longRawResourceIncident i v.val)

theorem long_raw_incidence_test_index_card_le_cube (n:ℕ) (hn:4≤n)
    (U:Type) [Fintype U] (hu:Fintype.card U≤n):
    Fintype.card (Fin n⊕LongRawIncidenceIndex n U)≤n^3 :=by
  simp only [LongRawIncidenceIndex,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_bool]
  have hn2:9≤n*n:=by nlinarith
  have hn3:9*n≤n^3:=by nlinarith [Nat.mul_le_mul_right n hn2]
  omega

theorem long_raw_surviving_resource_card_le_cube {n:ℕ} {U:Type}
    [Fintype U] [DecidableEq U] (hn:4≤n) (hu:Fintype.card U≤n)
    (S:Finset (LongRawHubResource n U)):
    Fintype.card S≤n^3 :=by
  exact (Fintype.card_subtype_le _).trans (long_typed_resource_card_le_cube n hn U hu)

end Oberwolfach
