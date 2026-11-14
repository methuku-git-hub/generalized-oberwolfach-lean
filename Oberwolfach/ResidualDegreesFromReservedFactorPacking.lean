module

public import Oberwolfach.BufferedCanonicalArcsPacking
public import Oberwolfach.ResidualDegreesFromReservedFactorArcs
public import Oberwolfach.ReservedFactorOrientationComplement

@[expose] public section
/-! Residual degree identities from physical packing of the original reserved factor remainders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_degrees_from_reserved_factor_packing
    {V U:Type*} [Fintype V] [DecidableEq V] [Fintype U]
    {I X K:U→Type*} [∀w,Fintype (I w)] [∀w,Fintype (X w)]
    [∀w,DecidableEq (X w)] [∀w,Fintype (K w)]
    (π:Equiv.Perm V) (c d:ℕ) (hc:0<c) (k:∀w,I w→ℕ)
    (hk:∀w j,0<k w j) (hkd:∀w j,k w j≤d) (a:∀w,I w→V)
    (hinj:∀w j,Function.Injective (fun i:Fin (k w j+1)=>(π^i.val) (a w j)))
    (hdisIntervals:∀w (j l:I w),j≠l→Disjoint (permutationWindow π 0 (k w j) (a w j))
      (permutationWindow π 0 (k w l) (a w l)))
    (huniform:∀v z,(Finset.univ.filter (fun w=>v∈markedIntervalRootSet π (k w) (a w))).card=
      (Finset.univ.filter (fun w=>z∈markedIntervalRootSet π (k w) (a w))).card)
    (G:∀w,SimpleGraph (X w)) (hG:∀w,(G w).IsRegularOfDegree 2)
    (components:∀w,K w↪(G w).ConnectedComponent)
    (e:∀w (i:K w),SimpleGraph.cycleGraph (Fintype.card (components w i)) ≃g (components w i).toSimpleGraph)
    (index:∀w,I w↪LongReservedBlockIndex (G w) (components w) c d)
    (H:Finset (V×V)):
    let n:=fun w i=>c*k w i
    let ext:=fun w i=>longReservedSigmaBlock (G w) (components w) c d (e w) (index w i) (k w i) (hkd w i)
    let inner:=fun w i=>longReservedInteriorEmbedding (n w i) (ext w i)
    let hinner:∀w i p,inner w i p=ext w i ⟨p.val+2,by have hp:p.val<c*k w i+1:=p.isLt;omega⟩:=by intro w i p;rfl
    let hdisPaths:∀w i j,i≠j→Disjoint (Finset.univ.image (ext w i)) (Finset.univ.image (ext w j)):=by
      intro w i j hij
      exact long_reserved_sigma_blocks_disjoint (G w) (components w) c d (e w) (index w i) (index w j)
        (k w i) (k w j) (hkd w i) (hkd w j) (fun h=>hij ((index w).injective h))
    let σ:=fun w=>factorCycleOrientation (G w) (extendComponentCycleChoices (G w) (hG w) (components w) (e w))
    let hσ:∀w,(complementTailDomain (bufferedPathFullDomain (n w) (inner w))
      (bufferedFinalEndpoints (n w) (inner w))).image (σ w)=
      complementTailDomain (bufferedPathFullDomain (n w) (inner w)) (bufferedInitialEndpoints (n w) (inner w)):=by
      intro w
      simpa only [complementTailDomain,bufferedInitialEndpoints] using
        reserved_factor_orientation_complement (G w) (hG w) (components w) (e w) c d hc (k w) (hkd w) (hk w) (index w)
    ∀(fC:∀w,{x // x∉bufferedPathStrictInterior (n w) (inner w)}↪V),
    (∀w i,fC w (bufferedInitialEndpointInComplement (n w) (ext w) (inner w) (hinner w) (hdisPaths w) i)=a w i)→
    (∀w i,fC w (bufferedEndpointInComplement (n w) (ext w) (inner w) (hinner w) (hdisPaths w) i)=(π^(k w i)) (a w i))→
    let tail:=fun w=>bufferedOrientedTailEmbedding (n w) (ext w) (inner w) (hinner w) (hdisPaths w) (fC w)
    let head:=fun w=>bufferedOrientedHeadEmbedding (n w) (ext w) (inner w) (hinner w) (hdisPaths w) (σ w) (hσ w) (fC w)
    (∀w,Finset.univ.image (fun x=>(tail w x,head w x))⊆H)→
    ∀(p:∀w i,(G w).Walk (inner w i 0) (inner w i (Fin.last (n w i))))
      (hlen:∀w i,(p w i).length=n w i) (hsupp:∀w i,(p w i).support=List.ofFn (inner w i)),
    let remaining:=fun w=>(((G w).deleteEdges (↑(Finset.univ.biUnion (fun i=>(p w i).edges.toFinset)):Set (Sym2 (X w)))).induce
      {x | x∉bufferedPathStrictInterior (n w) (inner w)}).edgeFinset.image (Sym2.map (fC w))
    (∀w z,w≠z→Disjoint (remaining w) (remaining z))→
    (∀v,(H.filter (fun e=>e.1=v)).card=Fintype.card U)→
    (∀v,(H.filter (fun e=>e.2=v)).card=Fintype.card U)→
    ∀v,(((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun x=>(tail w x,head w x)))).filter (fun e=>e.1=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (n w) (inner w) (fC w) ∪
        Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card) ∧
      (((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun x=>(tail w x,head w x)))).filter (fun e=>e.2=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (n w) (inner w) (fC w) ∪
        Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card):=by
  intro n ext inner hinner hdisPaths σ hσ fC hstart hfinish tail head hsub p hlen hsupp remaining hpack hHout hHin
  have hstep:∀w i (j:Fin (n w i)),σ w (inner w i j.castSucc)=inner w i j.succ:=by
    intro w i j
    have hj:j.val<c*k w i:=j.isLt
    have hh:=factor_cycle_orientation_reserved_block_step (G w) (hG w) (components w) (e w) c d (index w i) (k w i) (hkd w i)
      ⟨j.val+2,by omega⟩
    change σ w (ext w i ⟨j.val+2,by omega⟩)=ext w i ⟨j.val+1+2,by omega⟩
    simpa only [σ,ext,n,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  have hdis:∀w z,w≠z→Disjoint (Finset.univ.image (fun x=>(tail w x,head w x)))
      (Finset.univ.image (fun x=>(tail z x,head z x))):=by
    exact buffered_canonical_arcs_disjoint_of_remaining_edge_packing G hG
      (fun w=>extendComponentCycleChoices (G w) (hG w) (components w) (e w))
      n ext inner hinner hdisPaths hstep p hlen hsupp hσ fC hpack
  exact residual_degrees_from_canonical_arcs π k a hk hinj hdisIntervals huniform n ext inner hinner hdisPaths σ hσ fC
    hstart hfinish H hsub hdis hHout hHin
end Oberwolfach
