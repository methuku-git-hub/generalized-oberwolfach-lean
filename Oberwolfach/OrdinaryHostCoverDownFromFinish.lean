module

public import Oberwolfach.OrdinaryCombinePackingCleanupFinishInHost
public import Oberwolfach.OrdinaryGeneralHostCoverDownResult
public import Oberwolfach.OrdinarySequentialHostDecompositions
public import Oberwolfach.OrdinaryCleanupPostFacts
public import Oberwolfach.OrdinarySequentialWheelDecompositions
public import Oberwolfach.LongThreeGraphDegree

@[expose] public section
/-! Combine the approximate packing, cleanup and boundary finish into one
wheel decomposition of the edges removed from the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_host_coverdown_from_packing_cleanup_finish
    (m:ℕ) (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (R:SimpleGraph (V⊕U)) (t ν ρ:ℝ) (Kcap Dmax:ℕ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (M:OrdinaryUnreservedPackingData Q F H X Z R (m+1) t):
    let C:=ordinaryPackingUsedGraph Q F H X Z R (m+1) t M;
    let Q₁:=ordinaryPackingPostRim Q F H X Z R (m+1) t M;
    let H₁:=ordinaryPackingPostSpokes Q F H X Z R (m+1) t M;
    ∀(K:OrdinaryOutsideCleanupData Q₁ F H₁ X Z C (m+1) ν),
    let Q₂:=ordinaryCleanupPostRim Q₁ F H₁ X Z C (m+1) ν K;
    let H₂:=ordinaryCleanupPostSpokes Q₁ F H₁ X Z C (m+1) ν K;
    OrdinaryGeneralFinishHostResult Q₂ F H₂ X Z m Kcap Dmax ρ→
    OrdinaryGeneralHostCoverDownResult Q F H X Z (m+1)
      (ν+2*(ρ*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)):=by
  intro C Q₁ H₁ K Q₂ H₂ hfinish
  obtain ⟨A,S,hA,hS,hhost,hdec,hrem⟩:=ordinary_combine_packing_cleanup_finish_in_host
    m Q F H X Z R t ν ρ Kcap Dmax hbal hdiv M K hfinish
  obtain ⟨hinner,hnextS,hnextBal,hnextDiv,hroot,hdegree⟩:=hrem
  refine ⟨A,S,hA,hS,hhost,hroot,?_,?_,hdegree⟩
  · convert hnextBal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hnextDiv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
