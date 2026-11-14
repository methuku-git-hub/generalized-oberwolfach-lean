module

public import Oberwolfach.ResidualDegreesFromActualReservedPacking
public import Oberwolfach.RetainedMarkedMatchingInputs

@[expose] public section
/-! Discharge the reserved-factor interval hypotheses using one retained sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_sample_residual_degree_identities
    {V U Γ Color Kbad Jbad:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] [DecidableEq Kbad] [DecidableEq Jbad]
    {X K:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)] [∀w,Fintype (K w)]
    (π:Equiv.Perm V) (c d:ℕ) (hc:0<c) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (sample:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d sample g) t)
    (G:∀w,SimpleGraph (X w)) (hG:∀w,(G w).IsRegularOfDegree 2)
    (components:∀w,K w↪(G w).ConnectedComponent)
    (e:∀w (i:K w),SimpleGraph.cycleGraph (Fintype.card (components w i)) ≃g (components w i).toSimpleGraph)
    (index:∀w,retainedMarkedIndex π d sample g t J w↪LongReservedBlockIndex (G w) (components w) c d)
    (H:Finset (V×V)):
    let k:=fun w (_:retainedMarkedIndex π d sample g t J w)=>d
    let a:=fun w (j:retainedMarkedIndex π d sample g t J w)=>j.val
    let hk:∀w j,0<k w j:=by intro w j;exact lt_of_lt_of_le (by decide : 0<2) hd
    let hkd:∀w j,k w j≤d:=by intro w j;exact le_rfl
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
    ∀(data:∀w,ActualResidualData (K:=Kbad) (J:=Jbad) (G w))
      (hCycle:∀w,(data w).t.biUnion (fun j=>((data w).C j).support.toFinset)⊆(data w).Cembed)
      (ψ:∀w,X w→V) (Φ:∀w,{x // x∈(data w).remaining}→V)
      (hold:∀w (x:{x // x∉bufferedPathStrictInterior (n w) (inner w)}),x.val∈(data w).oldDomain→fC w x=ψ w x.val)
      (hnew:∀w (x:{x // x∉bufferedPathStrictInterior (n w) (inner w)}) (hx:x.val∈(data w).remaining),fC w x=Φ w ⟨x.val,hx⟩)
      (Pack:Finset (Sym2 V)),
    let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion (fun i=>(p w i).edges.toFinset))).image (Sym2.map (ψ w))
    let new:=fun w=>(((data w).graph.induce (↑(data w).remaining:Set (X w))).edgeFinset).image (Sym2.map (Φ w))
    (∀w z,w≠z→Disjoint (old w) (old z))→(∀w,old w⊆Pack)→
    (∀w z,w≠z→Disjoint (new w) (new z))→(∀w,Disjoint (new w) Pack)→
    (∀v,(H.filter (fun e=>e.1=v)).card=Fintype.card U)→
    (∀v,(H.filter (fun e=>e.2=v)).card=Fintype.card U)→
    ∀v,(((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun x=>(tail w x,head w x)))).filter (fun e=>e.1=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (n w) (inner w) (fC w) ∪
        Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card) ∧
      (((H\Finset.univ.biUnion (fun w=>Finset.univ.image (fun x=>(tail w x,head w x)))).filter (fun e=>e.2=v)).card=
      (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (n w) (inner w) (fC w) ∪
        Finset.univ.image (fun j=>(π^(k w j)) (a w j)))).card):=by
  intro k a hk hkd n ext inner hinner hdisPaths σ hσ fC hstart hfinish tail head hsub p hlen hsupp data hCycle ψ Φ hold hnew Pack old new holdPair holdPack hnewPair hnewPack hHout hHin
  have hgeom:=retained_marked_interval_geometry π d (by omega) hnoshort sample g t J
  exact residual_degrees_from_actual_reserved_factor_packing π c d hc k hk hkd a hgeom.1 hgeom.2.1 hgeom.2.2
    G hG components e index H fC hstart hfinish hsub p hlen hsupp data hCycle ψ Φ hold hnew Pack
    holdPair holdPack hnewPair hnewPack hHout hHin
end Oberwolfach
