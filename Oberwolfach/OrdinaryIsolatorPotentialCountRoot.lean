module

public import Oberwolfach.OrdinaryIsolatorPotential

@[expose] public section
/-! The aggregate root-omitted isolator potential is exactly the normalized
number of actual configurations when the root edge is present. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V]

theorem rooted_induced_survival_update_root {I:Type} [Fintype I] {k:ℕ}
    (P:SimpleGraph V) (S:I→FixedSubset V k) (root:Sym2 V) (σ:Sym2 V→Bool) (b:Bool):
    rootedInducedSurvivalSum P S root (Function.update σ root b)=rootedInducedSurvivalSum P S root σ:=by
  rw [rootedInducedSurvivalSum_card,rootedInducedSurvivalSum_card]
  congr 1
  have hc:Fintype.card {i:I // ∀e∈rootOmittedInducedEdges P (S i).val root,Function.update σ root b e=true}=
      Fintype.card {i:I // ∀e∈rootOmittedInducedEdges P (S i).val root,σ e=true}:=by
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro i
    constructor <;> intro h e he
    · have hne:e≠root:=(Finset.mem_erase.mp he).1
      simpa only [Function.update_of_ne hne] using h e he
    · have hne:e≠root:=(Finset.mem_erase.mp he).1
      simpa only [Function.update_of_ne hne] using h e he
  exact_mod_cast hc

theorem ordinary_isolator_potential_actual_count
    (P F:SimpleGraph V) (H:V→U→Prop) (k:ℕ) (hk:2≤k) (θ α:ℝ) (x y:V)
    (σ:Sym2 V→Bool) (hroot:(retainedGraph P σ).Adj x y):
    ordinaryIsolatorPotential P F H k θ α x y σ=
      (Fintype.card (OrdinaryIsolatorConfiguration P (retainedGraph P σ\F) F H k θ α x y):ℝ)/
        (Fintype.card V:ℝ)^(k-1):=by
  let C:=OrdinaryIsolatorConfiguration P (retainedGraph P σ\F) F H k θ α x y
  have hf (u:U):
      (if H x u∧H y u then rootedInducedSurvivalSum P
        (fun S:OrdinaryIsolatorCandidate P F H k θ α x y u=>S.val) s(x,y) σ else 0)=
      (Fintype.card {T:C // T.hub=u}:ℝ)/(Fintype.card V:ℝ)^(k-2):=by
    by_cases hu:H x u∧H y u
    · rw [if_pos hu]
      exact ordinary_isolator_potential_count_eq P F H k θ α x y u σ hroot hu.1 hu.2
    · rw [if_neg hu]
      have hempty:IsEmpty {T:C // T.hub=u}:=⟨fun T=>by
        apply hu
        have hx:=T.val.spokes x T.val.endpoints.1
        have hy:=T.val.spokes y T.val.endpoints.2
        simpa only [T.property] using And.intro hx hy⟩
      simp only [Fintype.card_eq_zero, Nat.cast_zero, zero_div]
  unfold ordinaryIsolatorPotential
  simp_rw [hf]
  rw [←Finset.sum_div,←finite_card_eq_sum_fibres (fun T:C=>T.hub)]
  have hexp:k-1=(k-2)+1:=by omega
  rw [hexp,pow_succ,div_mul_eq_div_div]
end Oberwolfach
