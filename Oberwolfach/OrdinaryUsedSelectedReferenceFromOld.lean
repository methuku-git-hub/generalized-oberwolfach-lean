module

public import Oberwolfach.OrdinaryOldAvoidsSelectedReference
public import Oberwolfach.OrdinaryComplementReferenceDegreeInputs

@[expose] public section
/-! The old matched pieces avoid the selected reference. Thus all selected
reference edges used by the complement are charged to the new residual union. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_used_selected_reference_degree_from_old
    {n q : ℕ} {Γ Color : Type} [Fintype Γ] [Fintype Color]
    {A B J : Fin q → Type} [∀u,Fintype (A u)] [∀u,DecidableEq (A u)]
    [∀u,DecidableEq (B u)] [∀u,DecidableEq (J u)]
    (P Host Del Reference : SimpleGraph (Fin n)) (hHost : Host≤P)
    (π : Equiv.Perm (Fin n)) (d : ℕ)
    (σ : ∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Γ Color e)
    (hReference : Reference≤rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e)))
    (Fs : Fin q→SimpleGraph (Fin n)) (C : ∀u,Finset (Fs u).ConnectedComponent)
    (f : ∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (data : ∀u,ActualResidualData (K:=A u⊕B u) (J:=J u)
      ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}))
    (hempty : ∀u,IsEmpty (A u)) (hs : ∀u,(data u).s₁=firstSumIndices)
    (ψ : ∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}→Fin n)
    (New : Fin q→Finset (Sym2 (Fin n)))
    (hdir : ∀u,ActualOldImageDirected (data u) (ψ u) (rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset)))
    (hpartition : ∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=(data u).deletedEdges.image (Sym2.map (ψ u)) ∪ New u)
    (loss : ℝ) (hnew : ∀v,((prescribedPhysicalUnion New).degree v:ℝ)≤loss) :
    ∀v,((Reference⊓ordinaryEmbeddedComplements Fs C f).degree v:ℝ)≤loss := by
  have hold : ∀u, Disjoint ((data u).deletedEdges.image (Sym2.map (ψ u))) Reference.edgeFinset := by
    intro u
    have hh := ordinary_old_edges_avoid_selected_reference P Host Del hHost π d σ (data u) (hempty u) (hs u) (ψ u) (hdir u)
    have hh' : Disjoint ((data u).deletedEdges.image (Sym2.map (ψ u)))
        (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))).edgeFinset := by
      convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    exact hh'.mono_right (SimpleGraph.edgeFinset_mono hReference)
  have hsub := ordinary_used_reference_degree_from_new_union Reference Fs C f
    (fun u=>(data u).deletedEdges.image (Sym2.map (ψ u))) New hpartition hold
  intro v
  have hh := SimpleGraph.degree_le_of_le hsub (v:=v)
  have hh' : ((Reference⊓ordinaryEmbeddedComplements Fs C f).degree v:ℝ)≤(prescribedPhysicalUnion New).degree v := by
    exact_mod_cast hh
  exact hh'.trans (hnew v)
end Oberwolfach
