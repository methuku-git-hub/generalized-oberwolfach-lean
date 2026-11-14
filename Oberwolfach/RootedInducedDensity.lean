module

public import Oberwolfach.RootedSubsetDensity
public import Oberwolfach.SelectedSetUnionBound
public import Oberwolfach.FractionalSubgraphs

@[expose] public section

/-! A uniform bound for failure of induced minimum degree, conditional on
fixed root vertices. Only selected vertices contribute to the union bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixedSubset_dense_neighbourhoods {V : Type*} [Fintype V] [DecidableEq V]
    (T : Finset V) (m : ℕ) (hm : m≤Fintype.card V) (hTm : T.card+1<m)
    [Nonempty (FixedSubset V m)] (A : V → Finset V)
    (δ α : ℝ) (hα : 0<α) (hA : ∀ x,(δ+α)*Fintype.card V≤((A x).card:ℝ))
    (hroots : (T.card:ℝ)+1≤α*m/4) :
    (FiniteLaw.uniform (FixedSubset V m)).probability
      (fun S => T⊆S.val ∧ ∃ x∈S.val,((A x∩S.val).card:ℝ)≤(δ+α/2)*m)≤
      (2*Real.exp (-α^2*m/8))*m*
        (FiniteLaw.uniform (FixedSubset V m)).probability (fun S => T⊆S.val) := by
  apply selected_set_union_bound (FiniteLaw.uniform (FixedSubset V m))
    (fun S => S.val) m (fun S => S.property) (fun S => T⊆S.val)
    (fun x S => ((A x∩S.val).card:ℝ)≤(δ+α/2)*m) (2*Real.exp (-α^2*m/8))
  intro x
  let T' := insert x T
  have hcard : T'.card≤T.card+1 := Finset.card_insert_le _ _
  have hT' : T'.card<m := lt_of_le_of_lt hcard hTm
  letI : Nonempty {S : FixedSubset V m // T'⊆S.val} := fixedSubset_containing_nonempty T' m hT'.le hm
  have hroots' : (T'.card:ℝ)≤α*m/4 := by
    have hh : (T'.card:ℝ)≤(T.card:ℝ)+1 := by exact_mod_cast hcard
    exact hh.trans hroots
  have hb := fixedSubset_rooted_low_count T' (A x) m hT' hm δ α hα (hA x) hroots'
  have hh : (FiniteLaw.uniform (FixedSubset V m)).probability
      (fun S => (T'⊆S.val) ∧ ((A x∩S.val).card:ℝ)≤(δ+α/2)*m)≤
      (FiniteLaw.uniform (FixedSubset V m)).probability (fun S => T'⊆S.val)*
        (2*Real.exp (-α^2*m/8)) := by
    rw [uniform_probability_intersection (fun S : FixedSubset V m => T'⊆S.val)
      (fun S => ((A x∩S.val).card:ℝ)≤(δ+α/2)*m)]
    apply mul_le_mul_of_nonneg_left _ (finiteLaw_probability_nonneg _ _)
    exact hb
  simpa only [T',Finset.insert_subset_iff,and_assoc,and_comm,and_left_comm,mul_comm] using hh

end Oberwolfach
