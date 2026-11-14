module

public import Oberwolfach.OrdinaryInducedWheelEquiv

@[expose] public section
/-! Transport wheel weights through the exact induced-domain equivalence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_wheel_adj (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (r:ℕ)
    (W:{W:OrdinaryWheel Q F H r // (ordinaryWheelRim W).support⊆A ∧ ordinaryWheelHub W∈B}) (x y:A):
    (ordinaryWheelRim (ordinaryInducedWheel Q F H A B r W)).Adj x y ↔
      (ordinaryWheelRim W.val).Adj x.val y.val:=by
  have he:=ordinary_induced_wheel_rim_map Q F H A B r W
  rw [←he]
  exact SimpleGraph.map_adj_apply.symm

theorem ordinary_induced_wheel_support (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (r:ℕ)
    (W:{W:OrdinaryWheel Q F H r // (ordinaryWheelRim W).support⊆A ∧ ordinaryWheelHub W∈B}) (x:A):
    x∈(ordinaryWheelRim (ordinaryInducedWheel Q F H A B r W)).support ↔
      x.val∈(ordinaryWheelRim W.val).support:=by
  have he:=ordinary_induced_wheel_rim_map Q F H A B r W
  rw [←he,SimpleGraph.support_map]
  constructor
  · intro hx;exact ⟨x,hx,rfl⟩
  · rintro ⟨y,hy,heq⟩
    have hxy:x=y:=Subtype.val_injective heq.symm
    simpa [hxy] using hy

def ordinaryInducedWheelWeight (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (r:ℕ)
    (w:OrdinaryWheel Q F H r→ℝ):
    OrdinaryWheel (Q.induce (A:Set V)) (F.induce (A:Set V)) (fun (v:A) (u:B)=>H v.val u.val) r→ℝ:=
  fun C=>w ((ordinaryInducedWheelEquiv Q F H A B r).symm C).val

theorem ordinary_induced_weight_rim_identity (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (r:ℕ)
    (w:OrdinaryWheel Q F H r→ℝ) (x y:A):
    ordinaryRimLoad (ordinaryInducedWheelWeight Q F H A B r w) x y=
      ∑ W:{W:OrdinaryWheel Q F H r // (ordinaryWheelRim W).support⊆A ∧ ordinaryWheelHub W∈B},
        if (ordinaryWheelRim W.val).Adj x.val y.val then w W.val else 0:=by
  unfold ordinaryRimLoad
  rw [←Equiv.sum_comp (ordinaryInducedWheelEquiv Q F H A B r)]
  apply Finset.sum_congr rfl
  intro W _
  let e:=ordinaryInducedWheelEquiv Q F H A B r
  change (if (ordinaryWheelRim (e W)).Adj x y then w (e.symm (e W)).val else 0)=_
  rw [e.symm_apply_apply]
  change (if (ordinaryWheelRim (ordinaryInducedWheel Q F H A B r W)).Adj x y then w W.val else 0)=_
  rw [ordinary_induced_wheel_adj]

theorem ordinary_induced_weight_spoke_identity (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (r:ℕ)
    (w:OrdinaryWheel Q F H r→ℝ) (v:A) (u:B):
    ordinarySpokeLoad (ordinaryInducedWheelWeight Q F H A B r w) v u=
      ∑ W:{W:OrdinaryWheel Q F H r // (ordinaryWheelRim W).support⊆A ∧ ordinaryWheelHub W∈B},
        if ordinaryWheelHub W.val=u.val ∧ v.val∈(ordinaryWheelRim W.val).support then w W.val else 0:=by
  unfold ordinarySpokeLoad
  rw [←Equiv.sum_comp (ordinaryInducedWheelEquiv Q F H A B r)]
  apply Finset.sum_congr rfl
  intro W _
  let e:=ordinaryInducedWheelEquiv Q F H A B r
  change (if ordinaryWheelHub (e W)=u ∧ v∈(ordinaryWheelRim (e W)).support then w (e.symm (e W)).val else 0)=_
  rw [e.symm_apply_apply]
  change (if ordinaryWheelHub (ordinaryInducedWheel Q F H A B r W)=u ∧
      v∈(ordinaryWheelRim (ordinaryInducedWheel Q F H A B r W)).support then w W.val else 0)=_
  have he:(ordinaryWheelHub (ordinaryInducedWheel Q F H A B r W)=u ∧
      v∈(ordinaryWheelRim (ordinaryInducedWheel Q F H A B r W)).support) ↔
      (ordinaryWheelHub W.val=u.val ∧ v.val∈(ordinaryWheelRim W.val).support):=by
    constructor
    · rintro ⟨hh,hv⟩
      exact ⟨congrArg Subtype.val hh,(ordinary_induced_wheel_support Q F H A B r W v).mp hv⟩
    · rintro ⟨hh,hv⟩
      exact ⟨Subtype.ext hh,(ordinary_induced_wheel_support Q F H A B r W v).mpr hv⟩
  by_cases hp:ordinaryWheelHub (ordinaryInducedWheel Q F H A B r W)=u ∧
      v∈(ordinaryWheelRim (ordinaryInducedWheel Q F H A B r W)).support
  · have hq:=he.mp hp
    simp only [hp,hq,if_true]
  · have hq:¬(ordinaryWheelHub W.val=u.val ∧ v.val∈(ordinaryWheelRim W.val).support):=fun h=>hp (he.mpr h)
    simp only [hp,hq,if_false]

end Oberwolfach
