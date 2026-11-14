module

public import Oberwolfach.OrdinaryTrackedWheelCertificateInputs
public import Oberwolfach.OrdinaryTrackedWheelReferenceData
public import Oberwolfach.OrdinaryVortexReferenceAbsorberChain

@[expose] public section
/-! Split the wheel chain from the construction of the reference and
absorber data, avoiding a single large elaboration. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_reference_local_wheel {n q r mAbs:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q → SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (Wterm:Finset (Fin n)) (Bterm:Finset (Fin q)) (hsize:Wterm.card+Bterm.card ≤ mAbs)
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (D mv:ℕ) (β ε:ℝ) (Vor:Vortex (Fin q) P D β ε mv)
    (L:ℕ) (hL:0<L) (cost deepCost:ℕ → ℝ)
    (hc:∀i,0 ≤ cost i) (hd:∀i,0 ≤ deepCost i)
    (hWterm:Vor.extendedVertices L=Wterm) (hBterm:Vor.extendedIndices L=Bterm)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hData:OrdinaryTrackedWheelReferenceData P S π d r mAbs σ Fs C Wterm Bterm Kabs f)
    (hcert:OrdinaryTrackedWheelCertificateInputs P S (permutationConflictGraph π (3*d)) Fs C r Kabs
      D mv β ε Vor L cost deepCost f):
    HasOrdinaryWheelDecomposition (S\ordinaryEmbeddedComplements Fs C f) (fun v u=>v∉Set.range (f u)) r :=by
  unfold OrdinaryTrackedWheelReferenceData at hData
  obtain ⟨hbal,hdiv,hP,hH,hA,hdec,hres⟩:=hData
  have hcall:=ordinary_vortex_reference_absorber_chain P D mv β ε Vor
    (S\ordinaryEmbeddedComplements Fs C f)
    (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\permutationConflictGraph π (3*d))
    (permutationConflictGraph π (3*d)) (fun v u=>v∉Set.range (f u))
    (rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false)
    r mAbs Wterm Bterm hsize
  have hFin:(fun (a b:Fin n)=>Classical.propDecidable (a=b))=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [hFin] at hcall
  refine hcall ?_ ?_ ?_ ?_ Kabs ?_ ?_ ?_
    L hL cost deepCost hc hd hWterm hBterm ?_
  · intro v
    have hh:=hbal v
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  · intro u
    have hh:=hdiv u
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  · exact hP
  · exact hH
  · convert hA using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hdec using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hres using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hcert using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
end Oberwolfach
