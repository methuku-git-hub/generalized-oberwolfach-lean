module

public import Oberwolfach.InnerBoundaryTotalDegree
public import Oberwolfach.LongPrescribedSelectedExtraNoInner
public import Oberwolfach.LongSelectedLossOutsideRequiredSelectedBound
public import Oberwolfach.LongIneligibleUnionDegree

@[expose] public section
/-! The selected loss has small total degree on the inner set: dense
required edges cost only the spacing error, while all remaining selected
edges cross the boundary and are charged at their outside endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem long_matched_selected_inner_total_loss
    (P S Used Del:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Req:V→V→Prop) (Pack:Finset (Sym2 V)) (E:U→Finset (Sym2 V))
    (hSP:S≤P) (hPackFull:Pack=Used.edgeFinset)
    (hPack:Pack⊆(longApproximatePhysicalGraph P π d ω).edgeFinset)
    (hHost:prescribedPhysicalUnion E≤S) (δDel lossLocal:ℝ) (hLocal:0≤lossLocal)
    (hDel:∀v∈I,(Del.degree v:ℝ)≤δDel)
    (hOutside:∀v,v∉I→((prescribedPhysicalUnion E).degree v:ℝ)≤lossLocal):
    let Sel:=longSelectedPhysicalGraph P π d ω
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack
    let Loss:=prescribedPhysicalUnion E;
    (∀w,Disjoint (E w) ((spanningRestriction (S\Used) I)\Kplus).edgeFinset)→
    (∑v∈I,((Del⊔(Loss⊓longPhysicalStateGraph P ω {1})⊔longPreparationIneligibleGraph P π d).degree v:ℝ))≤
      (I.card:ℝ)*(δDel+2*((6*d+2:ℕ):ℝ))+(Fintype.card V:ℝ)*lossLocal :=by
  intro Sel K Kplus Loss hAvoid
  let X:SimpleGraph V:=(Loss\Kplus)⊓longPhysicalStateGraph P ω {1}
  have hinner:∀x∈I,∀y∈I,¬X.Adj x y:=by
    exact long_prescribed_selected_extra_no_inner_from_full_packing P S Used Kplus π d I ω E Pack hHost hAvoid hPackFull hPack
  have hXout:∀v,v∉I→(X.degree v:ℝ)≤lossLocal:=by
    intro v hv
    have hsub:X.neighborFinset v⊆Loss.neighborFinset v:=by
      intro w hw
      have hh:X.Adj v w:=(SimpleGraph.mem_neighborFinset _ _ _).mp hw
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr hh.1.1
    have hh:=Finset.card_le_card hsub
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hh
    have hh':(X.degree v:ℝ)≤(Loss.degree v:ℝ):=by exact_mod_cast hh
    exact hh'.trans (hOutside v hv)
  have hsumX:(∑v∈I,(X.degree v:ℝ))≤Fintype.card V*lossLocal:=by
    have hh:=inner_boundary_total_degree_bound X I lossLocal hinner hLocal
      (by intro v hv; have hh:=hXout v hv; convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hpoint:∀v∈I,((Del⊔(Loss⊓longPhysicalStateGraph P ω {1})⊔longPreparationIneligibleGraph P π d).degree v:ℝ)≤
      δDel+(X.degree v:ℝ)+2*((6*d+2:ℕ):ℝ):=by
    intro v hv
    have hthree:=long_three_graph_degree_bound Del (Loss⊓longPhysicalStateGraph P ω {1}) (longPreparationIneligibleGraph P π d) v
    have hsel:=long_selected_loss_outside_required_selected_bound P S Used Loss π d I ω Req Pack hSP hPackFull v
    have hbad:=long_preparation_ineligible_degree P π d v
    have ht:((Del⊔(Loss⊓longPhysicalStateGraph P ω {1})⊔longPreparationIneligibleGraph P π d).degree v:ℝ)≤
        (Del.degree v:ℝ)+((Loss⊓longPhysicalStateGraph P ω {1}).degree v:ℝ)+((longPreparationIneligibleGraph P π d).degree v:ℝ):=by
      have hh:(Del⊔(Loss⊓longPhysicalStateGraph P ω {1})⊔longPreparationIneligibleGraph P π d).degree v≤
          Del.degree v+(Loss⊓longPhysicalStateGraph P ω {1}).degree v+(longPreparationIneligibleGraph P π d).degree v:=by
        convert hthree using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
      exact_mod_cast hh
    have hs:((Loss⊓longPhysicalStateGraph P ω {1}).degree v:ℝ)≤(X.degree v:ℝ)+((6*d+2:ℕ):ℝ):=by
      have hh:(Loss⊓longPhysicalStateGraph P ω {1}).degree v≤X.degree v+(6*d+2):=by
        convert hsel using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
      exact_mod_cast hh
    have hb:((longPreparationIneligibleGraph P π d).degree v:ℝ)≤((6*d+2:ℕ):ℝ):=by exact_mod_cast hbad
    linarith [hDel v hv]
  have hsum:=Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hsum
  nlinarith [hsumX]
end Oberwolfach
