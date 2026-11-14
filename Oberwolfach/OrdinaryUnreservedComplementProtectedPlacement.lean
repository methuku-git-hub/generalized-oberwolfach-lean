module

public import Oberwolfach.OrdinaryUnreservedComplementFromMarkers
public import Oberwolfach.OrdinaryProtectedListRetainedRoots

@[expose] public section
/-! Glue a protected-list residual placement to the buffered old embedding;
the retained-root disjointness follows from the sampled protected list. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n r:ℕ} [Nonempty (Fin n)] {U Kbad Jbad:Type}
  [Fintype U] [DecidableEq U] [DecidableEq Kbad] [DecidableEq Jbad]

theorem ordinary_unreserved_complement_from_protected_placement
    (F₀:SimpleGraph (Fin n)) (hF₀:F₀.IsRegularOfDegree 2)
    (Cres:Finset F₀.ConnectedComponent) (hsize:∀c:↥Cres,Fintype.card c.val=r):
    let S:Set (Fin n):={x | F₀.connectedComponentMk x∉Cres}
    let X:=↥S
    let F:=F₀.induce S;
    ∀    (data:ActualResidualData (K:=Kbad) (J:=Jbad) F)
    (π:Equiv.Perm (Fin n)) (hd:2≤data.d)
    (hnoshort:∀x l,0<l→l<2*data.d+1→(π^l) x≠x)
    (sample:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π data.d sample false) t) (w:U)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (ext:∀i:retainedMarkedIndex π data.d sample false t J w,Fin (data.c*data.d+5)↪X)
    (inner:∀i:retainedMarkedIndex π data.d sample false t J w,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (index:retainedMarkedIndex π data.d sample false t J w→{i // i∈data.s₁})
    (hParent:∀i,(data.P (index i).val).support=List.ofFn (ext i))
        (ψ:X→Fin n) (hψ:Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner):Set X))
    (hmarker:∀i (j:Fin (data.d+1)),bufferedMarker data.c data.d (ext i) j∈data.prescribed→
      ψ (bufferedMarker data.c data.d (ext i) j)=(π^j.val) i.val)
    (B:Finset {x // x∈data.remaining}) (g Φ:{x // x∈data.remaining}→Fin n) (C:Finset (Fin n))
    (L:Finset (Fin n)) (hLdef:L=rawIntervalProtectedUnassignedList π data.d sample false true t J w)
    (hA₀B:residualSubtypeSet data.remaining data.prescribed⊆B) (hΦ:Function.Injective Φ)
    (hg:∀x∈residualSubtypeSet data.remaining data.prescribed,g x=ψ x.val) (hΦg:∀x∈B,Φ x=g x)
    (himage:B.image g=(residualSubtypeSet data.remaining data.prescribed).image (fun x=>ψ x.val)∪C)
    (hOldC:Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner).image ψ) C)
    (hfree:∀x,x∉B→Φ x∈L) (hL:Disjoint L ((data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner).image ψ)),
    let Y:=markedIntervalRootSet π (fun _ : retainedMarkedIndex π data.d sample false t J w=>data.d) Subtype.val
    (∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>data.c*data.d) inner→ψ x∉Y)→
    C⊆L→
    ∃fC:{x // x∉bufferedPathStrictInterior (fun _=>data.c*data.d) inner}↪Fin n,
      (∀x:{x // x∉bufferedPathStrictInterior (fun _=>data.c*data.d) inner},x.val∈data.oldDomain→fC x=ψ x.val) ∧
      (∀x:{x // x∈data.remaining},∀hx:x.val∉bufferedPathStrictInterior (fun _=>data.c*data.d) inner,fC ⟨x.val,hx⟩=Φ x) ∧
      (∀i,fC (bufferedInitialEndpointInComplement (fun _=>data.c*data.d) ext inner hinner hdis i)=i.val) ∧
      (∀i,fC (bufferedEndpointInComplement (fun _=>data.c*data.d) ext inner hinner hdis i)=(π^data.d) i.val) ∧
      let R:=Finset.univ\(outsideBufferedPathImage (fun _=>data.c*data.d) inner fC ∪
        Finset.univ.image (fun i:retainedMarkedIndex π data.d sample false t J w=>(π^data.d) i.val))
      Y⊆R ∧ R.card=r*Cres.card+data.c*Y.card ∧ Disjoint (R\Y) (Y.image π) :=by
  intro S X F data π hd hnoshort sample t J w hCycle ext inner hinner hdis index hParent ψ hψ hmarker B g Φ C L hLdef hA₀B hΦ hg hΦg himage hOldC hfree hL Y hOldAvoid hCsub
  have hLY:Disjoint L Y:=by
    rw [hLdef]
    exact ordinary_protected_list_disjoint_retained_roots π data.d (by omega) sample t J w
  have hCY:Disjoint C Y:=hLY.mono_left hCsub
  exact ordinary_unreserved_complement_from_buffered_markers F₀ hF₀ Cres hsize data π hd hnoshort sample false t J w hCycle
    ext inner hinner hdis index hParent ψ hψ hmarker B g Φ L C ∅ hA₀B hΦ hg hΦg
    (by simpa only [Finset.union_empty] using himage) hOldC (by simp) hfree hL hOldAvoid hCY (by simp) hLY
end Oberwolfach
