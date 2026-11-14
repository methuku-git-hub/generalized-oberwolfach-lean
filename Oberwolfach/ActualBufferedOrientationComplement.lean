module

public import Oberwolfach.BufferedOrientedSourceComplement
public import Oberwolfach.FactorCycleOrientationEdges

@[expose] public section
/-! The globally oriented source retains the exact tail/head complement
identity for the reserved paths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_buffered_orientation_complement
    {X A B:Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [DecidableEq B]
    (G:SimpleGraph X) (E:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (c d:ℕ) (hc:0<c) (hd:0<d)
    (ext:∀i:A⊕B,Fin (c*d+5)↪X) (inner:∀i:A,Fin (c*d+1)↪X)
    (hinner:∀i p,inner i p=ext (.inl i) ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (hstep:∀i (j:Fin (c*d+4)),factorCycleOrientation G E (ext i j.castSucc)=ext i j.succ):
    ((Finset.univ\bufferedPathFullDomain (fun _:A=>c*d) inner)∪bufferedFinalEndpoints (fun _:A=>c*d) inner).image (factorCycleOrientation G E)=
      (Finset.univ\bufferedPathFullDomain (fun _:A=>c*d) inner)∪Finset.univ.image (fun i=>inner i 0):=by
  let extA:=fun i:A=>ext (.inl i)
  have hdisA:∀i j,i≠j→Disjoint (Finset.univ.image (extA i)) (Finset.univ.image (extA j)):=by
    intro i j hij
    exact hdis (.inl i) (.inl j) (by simpa using hij)
  have hstepA:∀i (j:Fin (c*d)),factorCycleOrientation G E (inner i j.castSucc)=inner i j.succ:=by
    intro i j
    rw [hinner,hinner]
    have hh:=hstep (.inl i) ⟨j.val+2,by omega⟩
    change factorCycleOrientation G E (ext (.inl i) ⟨j.val+2,by omega⟩)=ext (.inl i) ⟨j.val+2+1,by omega⟩ at hh
    simpa only [Fin.val_mk,Fin.val_castSucc,Fin.val_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  exact buffered_oriented_source_complement (fun _:A=>c*d) extA inner hinner hdisA (factorCycleOrientation G E)
    (fun _=>Nat.mul_pos hc hd) hstepA
end Oberwolfach
