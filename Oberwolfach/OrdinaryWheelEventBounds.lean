module

public import Oberwolfach.ProductEventBounds
public import Oberwolfach.OrdinaryWheelLoads
public import Oberwolfach.OrdinaryCyclePairLoads

@[expose] public section

/-! Weighted counts of actual ordinary wheels with specified rim vertices
and allowed hubs. The same fixed weights are used for every event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem ordinary_wheel_event_weight_bound {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    (Q F : SimpleGraph V) (H : V → U → Prop) (r : ℕ) (hr : 2≤r) (hn : 0<Fintype.card V)
    (w : OrdinaryWheel Q F H r → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
    (S : Finset V) (hS : 2≤S.card) (T : Finset U)
    (P : OrdinaryWheel Q F H r → Prop)
    (hP : ∀ W,P W → (↑S:Set V)⊆(ordinaryWheelRim W).support ∧ ordinaryWheelHub W∈T) :
    (∑ W,if P W then w W else 0)≤
      (T.card:ℝ)*(r:ℝ)^S.card*B/(Fintype.card V:ℝ)^(S.card-1) := by
  classical
  let n : ℝ := Fintype.card V
  have hn0 : 0<n := Nat.cast_pos.mpr hn
  let M : ℝ := B/n^(r-1)
  have hM : 0≤M := by dsimp only [M];positivity
  have hnorm (t : ℕ) (ht : 2≤t) : B/n^(t-1)=(B/n)/n^(t-2) := by
    have hp : n^(t-1)=n^(t-2)*n := by rw [← pow_succ,show t-2+1=t-1 by omega]
    rw [hp];field_simp
  have hcycle := ordinary_cycle_event_weight_bound Q r (by omega) hn (fun _=>M) (fun _=>hM)
    (B/n) (by positivity) (fun _=>by dsimp only [M];rw [hnorm r hr]) S hS
    (fun C : OrdinaryCycle Q r=>(↑S:Set V)⊆C.val.val.support) (fun _ h=>h)
  have he := product_subtype_event_bound
    (fun W : OrdinaryCycle Q r × U=>
      (∀ v∈W.1.val.val.support,H v W.2) ∧
      (∀ v∈W.1.val.val.support,∀ u∈W.1.val.val.support,¬F.Adj v u))
    w M hM (fun W=>(hw W).2) (fun C=>(↑S:Set V)⊆C.val.val.support) T P hP
  calc
    _ ≤ (T.card:ℝ)*(∑ C : OrdinaryCycle Q r,if (↑S:Set V)⊆C.val.val.support then M else 0) := by
      convert (config := {closePre:=false,closePost:=false}) he using 1
      · apply Finset.sum_congr
        · ext W;simp
        · intro W _;rfl
    _ ≤ (T.card:ℝ)*((r:ℝ)^S.card*(B/n)/n^(S.card-2)) :=
      by
        convert mul_le_mul_of_nonneg_left hcycle (show (0:ℝ)≤T.card by positivity) using 1
    _ = _ := by
      have he : (T.card:ℝ)*((r:ℝ)^S.card*(B/n)/n^(S.card-2))=
          (T.card:ℝ)*(r:ℝ)^S.card*((B/n)/n^(S.card-2)) := by ring
      rw [he,← hnorm S.card hS]
      dsimp only [n]
      ring

end Oberwolfach
