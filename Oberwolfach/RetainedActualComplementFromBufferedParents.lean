module

public import Oberwolfach.RetainedActualComplementSpokeConstruction
public import Oberwolfach.ActualBufferedFinalPathIdentification
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

variable {X V U Γ Color Kbad Jbad:Type} [Fintype X] [DecidableEq X]
  [Fintype V] [DecidableEq V] [Nonempty V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color] [DecidableEq Kbad] [DecidableEq Jbad]

theorem retained_actual_complement_from_buffered_parents
    (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2)
    (data:ActualResidualData (K:=Kbad) (J:=Jbad) F)
    (π:Equiv.Perm V) (hd:2≤data.d)
    (hnoshort:∀x l,0<l→l<2*data.d+1→(π^l) x≠x)
    (sample:RawIntervalFamilyOutcome V U Γ Color) (colour:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π data.d sample colour) t) (w:U)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (ext:∀i:retainedMarkedIndex π data.d sample colour t J w,Fin (data.c*data.d+5)↪X)
    (inner:∀i:retainedMarkedIndex π data.d sample colour t J w,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (index:retainedMarkedIndex π data.d sample colour t J w→{i // i∈data.s₁})
    (hParent:∀i,(data.P (index i).val).support=List.ofFn (ext i))
    (hcard:Fintype.card X=Fintype.card V)
    (ψ:X→V) (hψ:Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner):Set X))
    (hψstart:∀i,ψ (data.start (.inl (index i)))=i.val)
    (hψfinish:∀i,ψ (data.finish (.inl (index i)))=(π^data.d) i.val)
    (B:Finset {x // x∈data.remaining}) (g Φ:{x // x∈data.remaining}→V) (L C Z:Finset V)
    (hA₀B:residualSubtypeSet data.remaining data.prescribed⊆B) (hΦ:Function.Injective Φ)
    (hg:∀x∈residualSubtypeSet data.remaining data.prescribed,g x=ψ x.val) (hΦg:∀x∈B,Φ x=g x)
    (himage:B.image g=(residualSubtypeSet data.remaining data.prescribed).image (fun x=>ψ x.val)∪C∪Z)
    (hOldC:Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner).image ψ) C)
    (hOldZ:Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner).image ψ) Z)
    (hfree:∀x,x∉B→Φ x∈L) (hL:Disjoint L ((data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner).image ψ)):
    let Y:=markedIntervalRootSet π (fun _ : retainedMarkedIndex π data.d sample colour t J w=>data.d) Subtype.val
    (∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>data.c*data.d) inner→ψ x∉Y)→
    Disjoint C Y→Disjoint Z Y→Disjoint L Y→
    ∃fC:{x // x∉bufferedPathStrictInterior (fun _=>data.c*data.d) inner}↪V,
      (∀x:{x // x∉bufferedPathStrictInterior (fun _=>data.c*data.d) inner},x.val∈data.oldDomain→fC x=ψ x.val) ∧
      (∀x:{x // x∈data.remaining},∀hx:x.val∉bufferedPathStrictInterior (fun _=>data.c*data.d) inner,fC ⟨x.val,hx⟩=Φ x) ∧
      (∀i,fC (bufferedInitialEndpointInComplement (fun _=>data.c*data.d) ext inner hinner hdis i)=i.val) ∧
      (∀i,fC (bufferedEndpointInComplement (fun _=>data.c*data.d) ext inner hinner hdis i)=(π^data.d) i.val) ∧
      let R:=Finset.univ\(outsideBufferedPathImage (fun _=>data.c*data.d) inner fC ∪
        Finset.univ.image (fun i:retainedMarkedIndex π data.d sample colour t J w=>(π^data.d) i.val))
      Y⊆R ∧ R.card=data.c*Y.card ∧ Disjoint (R\Y) (Y.image π):=by
  intro Y hOldAvoid hCY hZY hLY
  have hpaths (i:retainedMarkedIndex π data.d sample colour t J w):=
    actual_final_path_matches_buffered_sequence data (index i) (ext i) (inner i) (hinner i) (hParent i)
  exact retained_actual_complement_and_spoke_construction π data.c data.d hd hnoshort sample colour t J w
    F hF data hCycle ext inner hinner hdis index (fun i=>(hpaths i).1) (fun i=>(hpaths i).2.1)
    (fun i=>(hpaths i).2.2) hcard ψ hψ hψstart hψfinish B g Φ L C Z hA₀B hΦ hg hΦg himage hOldC hOldZ
    hfree hL hOldAvoid hCY hZY hLY
end Oberwolfach
