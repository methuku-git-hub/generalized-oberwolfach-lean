module

public import Oberwolfach.LongSelectedLossOutsideRequiredSelectedBound
public import Oberwolfach.LongIneligibleUnionDegree

@[expose] public section
/-! Convert an extra-edge degree bound into the marked-state inner loss
budget used by the two-rate matched correction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_matched_selected_extra_inner_loss_budget
    (P S Used Del Loss:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Req:V→V→Prop) (Pack:Finset (Sym2 V)) (hSP:S≤P) (hPack:Pack=Used.edgeFinset)
    (δDel δExtra:ℝ) (hDel:∀v∈I,(Del.degree v:ℝ)≤δDel):
    let Sel:=longSelectedPhysicalGraph P π d ω
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack;
    (∀v∈I,(((Loss\Kplus)⊓longPhysicalStateGraph P ω {1}).degree v:ℝ)≤δExtra)→
    ∀v∈I,((Del⊔(Loss⊓longPhysicalStateGraph P ω {1})⊔longPreparationIneligibleGraph P π d).degree v:ℝ)≤
      δDel+δExtra+2*((6*d+2:ℕ):ℝ) :=by
  intro Sel K Kplus hExtra v hv
  have hthree:=long_three_graph_degree_bound Del (Loss⊓longPhysicalStateGraph P ω {1}) (longPreparationIneligibleGraph P π d) v
  have hselected:=long_selected_loss_outside_required_selected_bound P S Used Loss π d I ω Req Pack hSP hPack v
  have hbad:=long_preparation_ineligible_degree P π d v
  have ht:((Del⊔(Loss⊓longPhysicalStateGraph P ω {1})⊔longPreparationIneligibleGraph P π d).degree v:ℝ)≤
      (Del.degree v:ℝ)+((Loss⊓longPhysicalStateGraph P ω {1}).degree v:ℝ)+
      ((longPreparationIneligibleGraph P π d).degree v:ℝ):=by
    have hh:(Del⊔(Loss⊓longPhysicalStateGraph P ω {1})⊔longPreparationIneligibleGraph P π d).degree v≤
        Del.degree v+(Loss⊓longPhysicalStateGraph P ω {1}).degree v+(longPreparationIneligibleGraph P π d).degree v:=by
      convert hthree using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    exact_mod_cast hh
  have hs:((Loss⊓longPhysicalStateGraph P ω {1}).degree v:ℝ)≤(((Loss\Kplus)⊓longPhysicalStateGraph P ω {1}).degree v:ℝ)+((6*d+2:ℕ):ℝ):=by
    have hh:(Loss⊓longPhysicalStateGraph P ω {1}).degree v≤((Loss\Kplus)⊓longPhysicalStateGraph P ω {1}).degree v+(6*d+2):=by
      convert hselected using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    exact_mod_cast hh
  have hb:((longPreparationIneligibleGraph P π d).degree v:ℝ)≤((6*d+2:ℕ):ℝ):=by exact_mod_cast hbad
  linarith [hDel v hv,hExtra v hv]
end Oberwolfach
