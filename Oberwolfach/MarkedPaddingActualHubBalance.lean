module

public import Oberwolfach.MarkedPaddingHubDegrees
public import Oberwolfach.MarkedPaddedGraphOccurrences

@[expose] public section

/-! Push the exact marked/ordinary spoke ratio through the actual map of
hub occurrences into the host. Identifying old hubs preserves the ratio. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {S U H I:Type} [Fintype S] [Fintype U] [Fintype H] [Fintype I]
    [DecidableEq U] [DecidableEq H] [DecidableEq I]

theorem finite_typed_fiber_composition (u:S→U) (h:U→H) (j:S→Bool) (z:H) (t:Bool):
    Fintype.card {s:S // h (u s)=z∧j s=t}=
      ∑ y:{y:U // h y=z},Fintype.card {s:S // u s=y.val∧j s=t}:=by
  let e:{s:S // h (u s)=z∧j s=t}≃(Σ y:{y:U // h y=z},{s:S // u s=y.val∧j s=t}):={
    toFun:=fun s=>⟨⟨u s.val,s.property.1⟩,⟨s.val,rfl,s.property.2⟩⟩
    invFun:=fun s=>⟨s.2.val,(congrArg h s.2.property.1).trans s.1.property,s.2.property.2⟩
    left_inv:=fun s=>rfl
    right_inv:=by
      rintro ⟨⟨y,hy⟩,⟨s,hs,hj⟩⟩
      cases hs
      rfl}
  rw [Fintype.card_congr e,Fintype.card_sigma]

theorem typed_fiber_balance_pushforward (u:S→U) (h:U→H) (j:S→Bool) (m:ℕ)
    (hb:∀ y,Fintype.card {s:S // u s=y∧j s=false}=m*Fintype.card {s:S // u s=y∧j s=true}):
    ∀ z,Fintype.card {s:S // h (u s)=z∧j s=false}=m*Fintype.card {s:S // h (u s)=z∧j s=true}:=by
  intro z
  rw [finite_typed_fiber_composition,finite_typed_fiber_composition,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun y _=>hb y.val)

theorem actual_padding_hub_balance (u:S→U) (h:I→U) (js:S→Bool) (m:ℕ)
    (hb:∀ z,Fintype.card {s:S // u s=z∧js s=false}=m*Fintype.card {s:S // u s=z∧js s=true}):
    ∀ z,Fintype.card {s // actualPaddingSpokeHub (m:=m) u h s=z∧paddingSpokeType js m s=false}=
      m*Fintype.card {s // actualPaddingSpokeHub (m:=m) u h s=z∧paddingSpokeType js m s=true}:=by
  have hbase:=padding_hub_balance (I:=I) u js m hb
  have hpush:=typed_fiber_balance_pushforward (paddingSpokeHub (I:=I) u m)
    (Sum.elim id h) (paddingSpokeType js m) m hbase
  have he:(fun s=>Sum.elim id h (paddingSpokeHub (I:=I) u m s))=actualPaddingSpokeHub (m:=m) u h:=by
    funext s;cases s <;> rfl
  have he':∀ s,Sum.elim id h (paddingSpokeHub (I:=I) u m s)=actualPaddingSpokeHub (m:=m) u h s:=fun s=>congrFun he s
  simpa only [he'] using hpush

end Oberwolfach
