module

public import Oberwolfach.ActualSourceOrientationUniqueOutgoing
public import Oberwolfach.FactorOrientationNoTwoCycles

@[expose] public section
/-! Turn directed target walks into containment of the corresponding old
source arcs. The physical edge cover can use any mixture of path pieces. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem old_directed_arcs_from_walk_edge_cover
    {X V I:Type} [DecidableEq X] [DecidableEq V] [Fintype I]
    (σ:X→X) (D:X→X→Prop) (ψ:X→V) (H:Finset (V×V))
    (n:I→ℕ) (source:∀i,Fin (n i+1)→X) (target:∀i,Fin (n i+1)→V)
    (E:Finset (Sym2 X))
    (hcover:E⊆Finset.univ.biUnion (fun i=>Finset.univ.image
      (fun k:Fin (n i)=>s(source i k.castSucc,source i k.succ))))
    (hstep:∀i (k:Fin (n i)),σ (source i k.castSucc)=source i k.succ)
    (hmatch:∀i k,ψ (source i k)=target i k)
    (htarget:∀i (k:Fin (n i)),(target i k.castSucc,target i k.succ)∈H)
    (halign:∀x,D x (σ x))
    (hunique:∀x y z,D x y→D x z→y=z)
    (hno2:∀x,σ (σ x)≠x):
    ∀x y,s(x,y)∈E→D x y→(ψ x,ψ y)∈H:=by
  intro x y he hxy
  have hy:σ x=y:=(hunique x (σ x) y (halign x) hxy)
  obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp (hcover he)
  obtain ⟨k,_,hk⟩:=Finset.mem_image.mp hi
  change s(source i k.castSucc,source i k.succ)=s(x,y) at hk
  rcases Sym2.eq_iff.mp hk with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · subst x
    subst y
    simpa only [hmatch] using htarget i k
  · have htwo:σ (σ (source i k.castSucc))=source i k.castSucc:=by
      rw [hstep, hb, hy, ←ha]
    exact False.elim (hno2 _ htwo)

end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_old_directed_arcs_from_walk_edge_cover
    {X V I:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (pieces:List (PrescribedSourcePiece X)) (D:X→X→Prop)
    (hpair:pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀p∈pieces,p.OriginalValid D)
    (hArcs:∀x y,D x y↔(x,y)∈sourcePieceArcsUnion pieces)
    (halign:∀x,D x (factorCycleOrientation G e x))
    (ψ:X→V) (H:Finset (V×V))
    (n:I→ℕ) (source:∀i,Fin (n i+1)→X) (target:∀i,Fin (n i+1)→V)
    (E:Finset (Sym2 X))
    (hcover:E⊆Finset.univ.biUnion (fun i=>Finset.univ.image
      (fun k:Fin (n i)=>s(source i k.castSucc,source i k.succ))))
    (hstep:∀i (k:Fin (n i)),factorCycleOrientation G e (source i k.castSucc)=source i k.succ)
    (hmatch:∀i k,ψ (source i k)=target i k)
    (htarget:∀i (k:Fin (n i)),(target i k.castSucc,target i k.succ)∈H):
    ∀x y,s(x,y)∈E→D x y→(ψ x,ψ y)∈H:=by
  apply old_directed_arcs_from_walk_edge_cover (factorCycleOrientation G e) D ψ H n source target E hcover hstep hmatch htarget halign
  · exact actual_source_orientation_has_unique_outgoing pieces D hpair hvalid hArcs
  · exact factor_orientation_no_two_cycles G hG e
end Oberwolfach
