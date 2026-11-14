module

public import Oberwolfach.OrdinaryIsolatorPotentialCountRoot

@[expose] public section
/-! The root-omitted potential supplies actual isolator counts even when
the root edge was absent from the original sample: force that one edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V]

theorem ordinary_isolator_potential_update_root (P F:SimpleGraph V) (H:V→U→Prop)
    (k:ℕ) (θ α:ℝ) (x y:V) (σ:Sym2 V→Bool) (b:Bool):
    ordinaryIsolatorPotential P F H k θ α x y (Function.update σ s(x,y) b)=
      ordinaryIsolatorPotential P F H k θ α x y σ:=by
  unfold ordinaryIsolatorPotential
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  split_ifs with hh
  · exact rooted_induced_survival_update_root P
      (fun S:OrdinaryIsolatorCandidate P F H k θ α x y u=>S.val) s(x,y) σ b
  · rfl

theorem ordinary_isolator_potential_count_with_forced_root
    (P F:SimpleGraph V) (H:V→U→Prop) (k:ℕ) (hk:2≤k) (θ α β:ℝ) (x y:V)
    (σ:Sym2 V→Bool) (hn:0<Fintype.card V) (hxy:P.Adj x y)
    (hpotential:β≤ordinaryIsolatorPotential P F H k θ α x y σ):
    β*(Fintype.card V:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P
        (retainedGraph P (Function.update σ s(x,y) true)\F) F H k θ α x y):ℝ):=by
  have hroot:(retainedGraph P (Function.update σ s(x,y) true)).Adj x y:=by
    exact ⟨hxy,by simp⟩
  have hp:=ordinary_isolator_potential_actual_count P F H k hk θ α x y
    (Function.update σ s(x,y) true) hroot
  rw [ordinary_isolator_potential_update_root] at hp
  have hden:0<(Fintype.card V:ℝ)^(k-1):=by positivity
  exact (le_div_iff₀ hden).mp (hpotential.trans_eq hp)
end Oberwolfach
