module

public import Oberwolfach.OrdinaryReserveEditBudget
public import Oberwolfach.OrdinaryRootResources
public import Oberwolfach.OrdinaryResourceSubgraphs

@[expose] public section
/-! A bounded reservoir costs at most its number of used rows in each rim
edit count. A prescribed extra margin absorbs this finite cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_reservoir_rim_degree_le_rows
    (P:SimpleGraph V) (A:Finset (Sym2 V⊕(V×U))) (v:V):
    (ordinaryResourceRim P A).degree v≤(ordinaryResourceRows A).card:=by
  have hsub:A⊆ordinaryRootResources (ordinaryResourceRows A) (ordinaryResourceHubs A):=
    ordinaryRootResources_contains A _ _ (Finset.Subset.refl _) (Finset.Subset.refl _)
  have hneigh:(ordinaryResourceRim P A).neighborFinset v⊆ordinaryResourceRows A:=by
    intro w hw
    have ha:Sum.inl s(v,w)∈A:=((ordinaryResourceRim P A).mem_neighborFinset v w).mp hw |>.2
    exact ((ordinaryRootResources_rim_iff (ordinaryResourceRows A) (ordinaryResourceHubs A) v w).mp (hsub ha)).2
  have hh:=Finset.card_le_card hneigh
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hh

theorem ordinary_protected_reservoir_edit_budget
    (Target Sample Reference:SimpleGraph V) (A:Finset (Sym2 V⊕(V×U)))
    (b η:ℝ) (a:ℕ)
    (hEdit:∀v,((Finset.univ.filter (fun y=>Xor (Target.Adj v y) (Sample.Adj v y))).card:ℝ)≤b*Fintype.card V)
    (hRows:(ordinaryResourceRows A).card≤a) (hSmall:(a:ℝ)≤η*Fintype.card V):
    ∀v,((Finset.univ.filter (fun y=>Xor ((Target\ordinaryResourceRim Reference A).Adj v y)
      (Sample.Adj v y))).card:ℝ)≤(b+η)*Fintype.card V:=by
  intro v
  have hh:=ordinary_reserved_rim_edit_budget Target Sample (ordinaryResourceRim Reference A) v
  have hd:((ordinaryResourceRim Reference A).degree v:ℝ)≤a:=by
    exact_mod_cast (ordinary_reservoir_rim_degree_le_rows Reference A v).trans hRows
  have hc:((Finset.univ.filter (fun y=>Xor ((Target\ordinaryResourceRim Reference A).Adj v y)
      (Sample.Adj v y))).card:ℝ)≤
      (Finset.univ.filter (fun y=>Xor (Target.Adj v y) (Sample.Adj v y))).card+
      ((ordinaryResourceRim Reference A).degree v:ℝ):=by exact_mod_cast hh
  nlinarith [hEdit v]
end Oberwolfach
