module

public import Oberwolfach.RawOrdinaryIntervalPositionInjective
public import Oberwolfach.ResidualMissingSpokeBound
public import Oberwolfach.RawMarkedHubCounts

@[expose] public section
/-! Missing positions of the actual approximate intervals are bounded by
uncovered marked spokes of the same sampled hub. -/
set_option autoImplicit false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_ordinary_missing_positions_le_uncovered
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U)
    (s:Finset {x:V // rawIntervalColouredStart π d (fun e=>σ (w,e)) x true})
    (T:{x:V // rawIntervalColouredStart π d (fun e=>σ (w,e)) x true}→Finset ℕ)
    (hT:∀i∈s,T i⊆Finset.range d) (Covered:Finset V)
    (hcovered:∀i∈s,∀j<d,(π^j) i.val∈Covered→j∈T i):
    (∑i∈s,(d-(T i).card))≤
      ((Finset.univ.filter (fun v=>rawMarkedSpokes π d σ true true true v w))\Covered).card:=by
  let Available:=Finset.univ.filter (fun v=>rawMarkedSpokes π d σ true true true v w)
  apply residual_missing_positions_le_uncovered_spokes s d T hT (fun i j=>(π^j) i.val) Available Covered
  · intro i hi j hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change rawIntervalState π d (fun e=>σ (w,e)) ((π^j) i.val)=some (Sum.inl true)
    apply (rawIntervalState_interval_iff π d (fun e=>σ (w,e)) _ true).2
    refine ⟨i.val,i.property,?_⟩
    apply (permutationWindow_mem_iff π 0 (d-1) i.val _).mpr
    refine ⟨⟨j,by omega⟩,?_⟩
    simp
  · intro i hi j hj i' hi' j' hj' he
    exact raw_ordinary_interval_position_injective π d hd hnoshort σ t J w i i' j j' hj hj' he
  · exact hcovered
end Oberwolfach
