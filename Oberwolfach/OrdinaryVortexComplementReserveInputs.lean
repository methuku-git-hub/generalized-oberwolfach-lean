module

public import Oberwolfach.OrdinaryComplementReserveSizeInputs
public import Oberwolfach.MarkedFixedVortexGeometry
public import Oberwolfach.OrdinaryVortexBufferedDomains

@[expose] public section
/-! The buffered-root geometry and one inner-size threshold discharge the
sharp-reference complement and failure-budget hypotheses at a vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D mv:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε mv)

theorem ordinary_vortex_complement_reserve_inputs
    (i n₀ Nreserve Nclean:ℕ) (lam:ℝ) (hlam:lam≤1/4)
    (hsize:max (max (4*n₀) (4*Nreserve)) (max Nclean 64)≤
      (markedVortexInnerVertices Q i).card)
    (hroot:((ordinaryVortexBufferedVertices Q i 2).card:ℝ)+
      (ordinaryVortexBufferedHubs Q i 2).card≤lam*Fintype.card (markedVortexVertexType Q i)):
    let Vloc:=markedVortexVertexType Q i;let Uloc:=markedVortexHubType Q i;
    let T:=ordinaryVortexBufferedVertices Q i 2;let W:=ordinaryVortexBufferedHubs Q i 2;
    let A:=↥(Finset.univ\T);let B:=↥(Finset.univ\W);
    n₀≤Fintype.card A ∧ Nreserve≤Fintype.card (A⊕B) ∧ Nclean≤Fintype.card (Vloc⊕Uloc) ∧
    1/(Fintype.card (A⊕B):ℝ)≤(1/16:ℝ) ∧
    (1/16:ℝ)+2/(Fintype.card (Vloc⊕Uloc):ℝ)≤1/8:=by
  intro Vloc Uloc T W A B
  have hIV:(markedVortexInnerVertices Q i).card≤Fintype.card Vloc:=Finset.card_le_univ _
  have hlarge:max (max (4*n₀) (4*Nreserve)) (max Nclean 64)≤Fintype.card Vloc:=hsize.trans hIV
  have hV0:(0:ℝ)≤Fintype.card Vloc:=by positivity
  have hW0:(0:ℝ)≤W.card:=by positivity
  have hT:(T.card:ℝ)≤(1/4:ℝ)*Fintype.card Vloc:=by
    have hh:=mul_le_mul_of_nonneg_right hlam hV0
    linarith [hroot]
  have hlarge':max (max (4*n₀) (4*Nreserve)) (max Nclean 64)≤
      Fintype.card (markedVortexVertexType Q i):=by
    convert hlarge using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hh:=ordinary_complement_reserve_size_inputs T W n₀ Nreserve Nclean
    (by convert hT using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by omega) (by omega) (by omega) (by omega)
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
