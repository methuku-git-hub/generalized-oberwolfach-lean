module

public import Oberwolfach.OrdinaryWheelCodegrees

@[expose] public section
/-! Root exclusion costs only a small weighted load at a retained edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_rim_excluded_vertex_load (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hr:2≤r) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1))
    (x y z:V) (hxy:x≠y) (hxz:x≠z) (hyz:y≠z):
    (∑ C,if (ordinaryWheelRim C).Adj x y ∧ z∈(ordinaryWheelRim C).support then w C else 0)≤
      (r:ℝ)^3*B/Fintype.card V:=by
  have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hu':(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hu
  have hs:(∑ C,if (ordinaryWheelRim C).Adj x y ∧ z∈(ordinaryWheelRim C).support then w C else 0)=
      ∑u:U,∑C,if (ordinaryWheelRim C).Adj x y ∧ ordinaryWheelHub C=u ∧ z∈(ordinaryWheelRim C).support then w C else 0:=by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro C _
    by_cases hR:(ordinaryWheelRim C).Adj x y <;> by_cases hz:z∈(ordinaryWheelRim C).support <;>
      simp [hR,hz]
  rw [hs]
  calc
    _ ≤ ∑_u:U,(r:ℝ)^3*B/(Fintype.card V:ℝ)^2:=
      Finset.sum_le_sum (fun u _=>ordinary_wheel_rim_spoke_offroot Q F H r hr hn w B hB hw x y z hxy hxz hyz u)
    _ = (Fintype.card U:ℝ)*((r:ℝ)^3*B/(Fintype.card V:ℝ)^2):=by simp
    _ ≤ (Fintype.card V:ℝ)*((r:ℝ)^3*B/(Fintype.card V:ℝ)^2):=
      mul_le_mul_of_nonneg_right hu' (by positivity)
    _ = (r:ℝ)^3*B/Fintype.card V:=by field_simp

theorem ordinary_spoke_excluded_vertex_load (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hr:2≤r) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1))
    (v z:V) (u:U) (hvz:v≠z):
    (∑ C,if ordinaryWheelHub C=u ∧ v∈(ordinaryWheelRim C).support ∧ z∈(ordinaryWheelRim C).support then w C else 0)≤
      (r:ℝ)^4*B/Fintype.card V:=by
  have hne:(Sum.inr (v,u):Sym2 V⊕(V×U))≠Sum.inr (z,u):=by
    intro he;exact hvz (congrArg Prod.fst (Sum.inr.inj he))
  have hh:=ordinary_wheel_physical_pair_load Q F H r hr hn hu w B hB hw (.inr (v,u)) (.inr (z,u)) hne
  simpa only [ordinaryWheelResources_spoke,and_assoc,and_left_comm,and_self_left] using hh

theorem ordinary_rim_excluded_hub_load (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hr:2≤r) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1))
    (x y:V) (u:U):
    (∑ C,if (ordinaryWheelRim C).Adj x y ∧ ordinaryWheelHub C=u then w C else 0)≤
      (r:ℝ)^4*B/Fintype.card V:=by
  have hne:(Sum.inl s(x,y):Sym2 V⊕(V×U))≠Sum.inr (x,u):=by simp
  have hh:=ordinary_wheel_physical_pair_load Q F H r hr hn hu w B hB hw (.inl s(x,y)) (.inr (x,u)) hne
  simp only [ordinaryWheelResources_rim,SimpleGraph.mem_edgeSet,ordinaryWheelResources_spoke] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro C _
  have hx:(ordinaryWheelRim C).Adj x y→x∈(ordinaryWheelRim C).support:=SimpleGraph.Adj.mem_support_left
  by_cases h:(ordinaryWheelRim C).Adj x y
  · simp [h,hx h]
  · simp [h]
end Oberwolfach
