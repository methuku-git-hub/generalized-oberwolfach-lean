module

public import Oberwolfach.LongRequiredExtendedHost
public import Oberwolfach.SelectedHostAvoidsApproximatePacking
public import Oberwolfach.RawSelectedPhysicalNeighbourTests

@[expose] public section
/-! Construct the free and prescribed directed hosts for the first step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_first_required_extended_host
    {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    (P Del Used:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (D:V→V→Prop) (Pack:Finset (Sym2 V))
    (hPack:Pack⊆Used.edgeFinset) (hLayer:Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset):
    let P₀:=longPhysicalStateGraph P σ {0,1,2,3,4}\Used
    let Sel:=longSelectedPhysicalGraph P π d σ
    let Kbad:=longRequiredPhysicalGraph P P₀ Sel π d I D (fun x y=>Used.Adj x y)
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
    let Dstar:=fun x y=>Dfree x y ∨ Kbad.Adj x y
    (∀x y,Dfree x y→Dstar x y) ∧
    (∀x y,Kbad.Adj x y→Dstar x y ∨ Dstar y x) ∧
    (∀x y,Dstar x y→P.Adj x y) ∧
    Disjoint Kbad.edgeFinset Pack ∧
    (∀x y,Dfree x y→s(x,y)∉Pack):=by
  intro P₀ Sel Kbad Dfree Dstar
  have hP₀:P₀≤P\Used:=by
    intro x y h
    exact ⟨h.1.1,h.2⟩
  have hfree:∀x y,Dfree x y→P.Adj x y:=by
    intro x y h
    have hh:markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x y=1:=h.1
    have hR:=(markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x y).mp hh
    simpa using hR.2.1
  obtain ⟨hDD,hDstar,hHost,hdis⟩:=long_required_extended_host P P₀ Sel Used π d I D Dfree Pack hP₀ hPack hfree
  refine ⟨hDD,hDstar,hHost,hdis,?_⟩
  intro x y h
  exact selected_host_avoids_approximate_packing P π d σ Pack hLayer x y h.1
end Oberwolfach
