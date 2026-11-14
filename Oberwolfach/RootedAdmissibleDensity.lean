module

public import Oberwolfach.RootedGoodDensity
public import Oberwolfach.RootedAdditionalInclusion
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! Dense bounded induced sets avoiding every conflict edge, with fixed
prescribed roots and the original without-replacement law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rootedSubset_dense_conflict_free_probability {V : Type*} [Fintype V] [DecidableEq V]
    (P F : SimpleGraph V) (T : Finset V) (k : ℕ) (hk : T.card+k≤Fintype.card V) (hk2 : 2≤k)
    [Nonempty (RootedSubset V T k)] (δ α L : ℝ) (hα : 0<α)
    (hP : ∀ v,(δ+α)*Fintype.card V≤(P.degree v:ℝ))
    (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hT : ∀ x∈T,∀ y∈T,¬F.Adj x y)
    (hroots : (T.card:ℝ)+1≤α*(T.card+k:ℝ)/4) :
    let q : ℝ := (k:ℝ)/(Fintype.card V-T.card:ℕ)
    1-2*(T.card+k:ℝ)*Real.exp (-α^2*(T.card+k:ℝ)/8)-
        L*(2*(T.card:ℝ)*q+Fintype.card V*q^2)≤
      (FiniteLaw.uniform (RootedSubset V T k)).probability (fun S=>
        (∀ v∈S.val.val,(δ+α/2)*(T.card+k:ℝ)<((P.neighborFinset v∩S.val.val).card:ℝ)) ∧
        (∀ x∈S.val.val,∀ y∈S.val.val,¬F.Adj x y)) := by
  intro q
  letI : Nonempty (FixedSubset V (T.card+k)) := fixedSubset_nonempty hk
  let μ := FiniteLaw.uniform (RootedSubset V T k)
  let Dense : RootedSubset V T k → Prop := fun S=>
    ∀ v∈S.val.val,(δ+α/2)*(T.card+k:ℝ)<((P.neighborFinset v∩S.val.val).card:ℝ)
  let Good : RootedSubset V T k → Prop := fun S=>∀ x∈S.val.val,∀ y∈S.val.val,¬F.Adj x y
  let loss : ℝ := L*(2*(T.card:ℝ)*q+Fintype.card V*q^2)
  have hbad := rootedSubset_conflict_probability F T k hk L hF hT
  have hgood : 1-loss≤μ.probability Good := by
    have hc := finiteLaw_probability_compl μ
      (fun S=>∃ x∈S.val.val,∃ y∈S.val.val,F.Adj x y)
    have he : (fun S : RootedSubset V T k=>¬(∃ x∈S.val.val,∃ y∈S.val.val,F.Adj x y))=Good := by
      funext S
      apply propext
      simp only [Good,not_exists,not_and]
    rw [he] at hc
    change μ.probability (fun S=>∃ x∈S.val.val,∃ y∈S.val.val,F.Adj x y)≤loss at hbad
    linarith only [hc,hbad]
  have hd : 1-2*(T.card+k:ℝ)*Real.exp (-α^2*(T.card+k:ℝ)/8)≤μ.probability Dense := by
    have hh := fixedSubset_rooted_dense_probability T (T.card+k) hk (by omega)
      (fun v=>P.neighborFinset v) δ α hα
      (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hP)
      (by simpa only [Nat.cast_add] using hroots)
    simpa only [Nat.cast_add,μ,Dense] using hh
  have hh := finiteLaw_good_intersection μ Dense Good loss hgood
  exact (sub_le_sub_right hd loss).trans hh

end Oberwolfach
