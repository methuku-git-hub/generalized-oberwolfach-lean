module

public import Oberwolfach.OrdinarySharedReferenceRobustness

@[expose] public section
/-! Restricting an edited class to the original reference edges keeps the
reference neighbourhoods close on every later chosen vertex domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_shared_reference_restricted_edits
    {n:ℕ} {U Γ Color:Type} [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P S:SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)
    (hI:∀x∈I,∀y∈I,S.Adj x y↔(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y)
    (hedit:∀x,((Finset.univ.filter (fun y=>Xor (S.Adj x y)
      ((longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y))).card:ℝ)≤ξ*n):
    let R:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e));
    ∀A:Finset (Fin n),∀x,
      ((changed (A∩R.neighborFinset x) (A∩(R⊓S).neighborFinset x)).card:ℝ)≤ξ*n :=by
  intro R A x
  have hdeg:((R\S).degree x:ℝ)≤ξ*n:=
    (ordinary_shared_reference_robustness P S I ξ σ hI hedit).1 x
  have hsub:changed (A∩R.neighborFinset x) (A∩(R⊓S).neighborFinset x)⊆(R\S).neighborFinset x:=by
    intro y hy
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter,
      SimpleGraph.mem_neighborFinset] at hy
    apply ((R\S).mem_neighborFinset x y).mpr
    simp only [SimpleGraph.sdiff_adj,SimpleGraph.inf_adj] at *
    tauto
  have hh:=Finset.card_le_card hsub
  have hh':((changed (A∩R.neighborFinset x) (A∩(R⊓S).neighborFinset x)).card:ℝ)≤((R\S).degree x:ℝ):=by
    exact_mod_cast hh
  exact hh'.trans hdeg
end Oberwolfach
