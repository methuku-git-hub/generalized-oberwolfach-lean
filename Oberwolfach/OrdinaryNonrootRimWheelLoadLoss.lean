module

public import Oberwolfach.OrdinaryRimExcludedWheelFamilies
public import Oberwolfach.FiniteWeightedUniformUnion

@[expose] public section
/-! Quantitative wheel-load loss under simultaneous removal of vertices and
hubs, for an edge whose endpoints remain in the induced domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_rim_nonroot_wheel_load_loss (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hr:2≤r) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1))
    (T:Finset V) (W:Finset U) (x y:V) (hxy:x≠y) (hx:x∉T) (hy:y∉T):
    (∑ C,if (ordinaryWheelRim C).Adj x y ∧
      (ordinaryWheelHub C∈W ∨ ∃z∈T,z∈(ordinaryWheelRim C).support) then w C else 0)≤
      ((T.card:ℝ)+W.card)*((r:ℝ)^4*B/Fintype.card V):=by
  have hfamily:=ordinary_rim_excluded_wheel_families Q F H r hr hn hu w B hB hw T W x y hxy hx hy
  have hh:=finite_weighted_uniform_value_and_union W T
    (fun C:OrdinaryWheel Q F H r=>(ordinaryWheelRim C).Adj x y) ordinaryWheelHub
    (fun C z=>z∈(ordinaryWheelRim C).support) w ((r:ℝ)^4*B/Fintype.card V) (fun C=>(hw C).1)
    (by intro u huW;convert hfamily.1 u huW using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro z hz;convert hfamily.2 z hz using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have he:((W.card:ℝ)+T.card)*((r:ℝ)^4*B/Fintype.card V)=
      ((T.card:ℝ)+W.card)*((r:ℝ)^4*B/Fintype.card V):=by ring
  rw [←he]
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _

end Oberwolfach
