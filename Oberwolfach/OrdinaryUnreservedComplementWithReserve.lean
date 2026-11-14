module

public import Oberwolfach.RetainedActualComplementSpokeWithReserve
public import Oberwolfach.OrdinaryUnreservedFactorCardinality
public import Oberwolfach.OrdinaryUnreservedFactorPaths
public import Oberwolfach.MarkedVariableResidualSpokeBalanceReserve
public import Oberwolfach.ActualFinalInteriorDeletion
public import Oberwolfach.ActualFinalEndpointAgreement
public import Oberwolfach.RetainedActualResidualSpokes

@[expose] public section
/-! Construct the final-path complement injection and its retained spoke
identities from compatible old and newly embedded source data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {n r:ℕ} [Nonempty (Fin n)] {U Γ Color Kbad Jbad:Type}
  [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color] [DecidableEq Kbad] [DecidableEq Jbad]

theorem ordinary_unreserved_complement_and_spoke_construction
    (F₀:SimpleGraph (Fin n)) (hF₀:F₀.IsRegularOfDegree 2)
    (Cres:Finset F₀.ConnectedComponent) (hsize:∀c:↥Cres,Fintype.card c.val=r):
    let S:Set (Fin n):={x | F₀.connectedComponentMk x∉Cres}
    let X:=↥S
    let F:=F₀.induce S;
    ∀    (π:Equiv.Perm (Fin n)) (c d:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (sample:RawIntervalFamilyOutcome (Fin n) U Γ Color) (colour:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d sample colour) t) (w:U)
    (data:ActualResidualData (K:=Kbad) (J:=Jbad) F)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (ext:∀i:retainedMarkedIndex π d sample colour t J w,Fin (c*d+5)↪X)
    (inner:∀i:retainedMarkedIndex π d sample colour t J w,Fin (c*d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (index:retainedMarkedIndex π d sample colour t J w→{i // i∈data.s₁})
    (hstart:∀i,data.start (.inl (index i))=inner i 0)
    (hfinish:∀i,data.finish (.inl (index i))=inner i (Fin.last (c*d)))
    (hsupport:∀i,(data.path (.inl (index i))).support=List.ofFn (inner i))
    (ψ:X→Fin n) (hψ:Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner):Set X))
    (hψstart:∀i,ψ (data.start (.inl (index i)))=i.val)
    (hψfinish:∀i,ψ (data.finish (.inl (index i)))=(π^d) i.val)
    (B:Finset {x // x∈data.remaining}) (g Φ:{x // x∈data.remaining}→Fin n) (L C Z:Finset (Fin n))
    (hA₀B:residualSubtypeSet data.remaining data.prescribed⊆B) (hΦ:Function.Injective Φ)
    (hg:∀x∈residualSubtypeSet data.remaining data.prescribed,g x=ψ x.val) (hΦg:∀x∈B,Φ x=g x)
    (himage:B.image g=(residualSubtypeSet data.remaining data.prescribed).image (fun x=>ψ x.val)∪C∪Z)
    (hOldC:Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner).image ψ) C)
    (hOldZ:Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner).image ψ) Z)
    (hfree:∀x,x∉B→Φ x∈L) (hL:Disjoint L ((data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner).image ψ)),
    let Y:=markedIntervalRootSet π (fun _ : retainedMarkedIndex π d sample colour t J w=>d) Subtype.val
    (∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>c*d) inner→ψ x∉Y)→
    Disjoint C Y→Disjoint Z Y→Disjoint L Y→
    ∃fC:{x // x∉bufferedPathStrictInterior (fun _=>c*d) inner}↪Fin n,
      (∀x:{x // x∉bufferedPathStrictInterior (fun _=>c*d) inner},x.val∈data.oldDomain→fC x=ψ x.val) ∧
      (∀x:{x // x∈data.remaining},∀hx:x.val∉bufferedPathStrictInterior (fun _=>c*d) inner,fC ⟨x.val,hx⟩=Φ x) ∧
      (∀i,fC (bufferedInitialEndpointInComplement (fun _=>c*d) ext inner hinner hdis i)=i.val) ∧
      (∀i,fC (bufferedEndpointInComplement (fun _=>c*d) ext inner hinner hdis i)=(π^d) i.val) ∧
      let R:=Finset.univ\(outsideBufferedPathImage (fun _=>c*d) inner fC ∪
        Finset.univ.image (fun i:retainedMarkedIndex π d sample colour t J w=>(π^d) i.val))
      Y⊆R ∧ R.card=r*Cres.card+c*Y.card ∧ Disjoint (R\Y) (Y.image π):=by
  intro S X F π c d hd hnoshort sample colour t J w data hCycle ext inner hinner hdis index hstart hfinish hsupport ψ hψ hψstart hψfinish B g Φ L C Z hA₀B hΦ hg hΦg himage hOldC hOldZ hfree hL Y hOldAvoid hCY hZY hLY
  have hcard:Fintype.card X+r*Cres.card=Fintype.card (Fin n):=by
    have hh:=ordinary_unreserved_factor_cardinality F₀ Cres hsize
    have heq:Fintype.card (↑{x:Fin n | F₀.connectedComponentMk x∉Cres}:Type)=
        Fintype.card {x:Fin n // F₀.connectedComponentMk x∉Cres}:=by
      apply Fintype.card_congr
      exact Equiv.refl _
    simp only [X,S,Fintype.card_fin]
    omega
  have hF:F.IsRegularOfDegree 2:=(ordinary_unreserved_factor_paths F₀ hF₀ Cres).1
  exact retained_actual_complement_and_spoke_construction_with_reserve π c d hd hnoshort sample colour t J w F hF data hCycle
    ext inner hinner hdis index hstart hfinish hsupport (r*Cres.card) hcard ψ hψ hψstart hψfinish
    B g Φ L C Z hA₀B hΦ hg hΦg himage hOldC hOldZ hfree hL hOldAvoid hCY hZY hLY
end Oberwolfach
