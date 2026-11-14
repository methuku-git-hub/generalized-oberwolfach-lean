module

public import Oberwolfach.RetainedActualComplementSpokeConstruction
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

variable {X V U Γ Color Kbad Jbad:Type} [Fintype X] [DecidableEq X]
  [Fintype V] [DecidableEq V] [Nonempty V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color] [DecidableEq Kbad] [DecidableEq Jbad]

theorem retained_actual_complement_and_spoke_construction_with_reserve
    (π:Equiv.Perm V) (c d:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (sample:RawIntervalFamilyOutcome V U Γ Color) (colour:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d sample colour) t) (w:U)
    (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2)
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
    (reserved:ℕ) (hcard:Fintype.card X+reserved=Fintype.card V)
    (ψ:X→V) (hψ:Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner):Set X))
    (hψstart:∀i,ψ (data.start (.inl (index i)))=i.val)
    (hψfinish:∀i,ψ (data.finish (.inl (index i)))=(π^d) i.val)
    (B:Finset {x // x∈data.remaining}) (g Φ:{x // x∈data.remaining}→V) (L C Z:Finset V)
    (hA₀B:residualSubtypeSet data.remaining data.prescribed⊆B) (hΦ:Function.Injective Φ)
    (hg:∀x∈residualSubtypeSet data.remaining data.prescribed,g x=ψ x.val) (hΦg:∀x∈B,Φ x=g x)
    (himage:B.image g=(residualSubtypeSet data.remaining data.prescribed).image (fun x=>ψ x.val)∪C∪Z)
    (hOldC:Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner).image ψ) C)
    (hOldZ:Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner).image ψ) Z)
    (hfree:∀x,x∉B→Φ x∈L) (hL:Disjoint L ((data.oldDomain\bufferedPathStrictInterior (fun _=>c*d) inner).image ψ)):
    let Y:=markedIntervalRootSet π (fun _ : retainedMarkedIndex π d sample colour t J w=>d) Subtype.val
    (∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>c*d) inner→ψ x∉Y)→
    Disjoint C Y→Disjoint Z Y→Disjoint L Y→
    ∃fC:{x // x∉bufferedPathStrictInterior (fun _=>c*d) inner}↪V,
      (∀x:{x // x∉bufferedPathStrictInterior (fun _=>c*d) inner},x.val∈data.oldDomain→fC x=ψ x.val) ∧
      (∀x:{x // x∈data.remaining},∀hx:x.val∉bufferedPathStrictInterior (fun _=>c*d) inner,fC ⟨x.val,hx⟩=Φ x) ∧
      (∀i,fC (bufferedInitialEndpointInComplement (fun _=>c*d) ext inner hinner hdis i)=i.val) ∧
      (∀i,fC (bufferedEndpointInComplement (fun _=>c*d) ext inner hinner hdis i)=(π^d) i.val) ∧
      let R:=Finset.univ\(outsideBufferedPathImage (fun _=>c*d) inner fC ∪
        Finset.univ.image (fun i:retainedMarkedIndex π d sample colour t J w=>(π^d) i.val))
      Y⊆R ∧ R.card=reserved+c*Y.card ∧ Disjoint (R\Y) (Y.image π):=by
  intro Y hOldAvoid hCY hZY hLY
  have hDR:Disjoint (bufferedPathStrictInterior (fun _=>c*d) inner) data.remaining:=
    (actual_final_path_interiors_are_deleted data (fun _=>c*d) inner (fun i=>Sum.inl (index i)) hstart hfinish hsupport).2
  obtain ⟨fC,hold,hnew,havoid⟩:=actual_complement_embedding_preserves_reserved_labels_from_anchor_images
    data hF hCycle (fun _=>c*d) inner hDR ψ hψ B g Φ L C Z Y hA₀B hΦ hg hΦg himage hOldC hOldZ hfree hL
    hOldAvoid hCY hZY hLY
  have hends:=actual_final_endpoints_agree_with_complement data hF (fun _=>c*d) ext inner hinner hdis
    index hstart hfinish fC ψ (fun i=>i.val) (fun i=>(π^d) i.val) hold hψstart hψfinish
  refine ⟨fC,hold,hnew,hends.1,hends.2,?_⟩
  let R:=Finset.univ\(outsideBufferedPathImage (fun _=>c*d) inner fC ∪
    Finset.univ.image (fun i:retainedMarkedIndex π d sample colour t J w=>(π^d) i.val))
  have hgeom:=retained_marked_interval_geometry π d (by omega) hnoshort sample colour t J
  refine ⟨?_,?_,?_⟩
  · exact marked_interval_roots_in_residual π (fun _ : retainedMarkedIndex π d sample colour t J w=>d) Subtype.val
      (hgeom.1 w) (hgeom.2.1 w) (outsideBufferedPathImage (fun _=>c*d) inner fC) R havoid.symm rfl
  · exact marked_variable_residual_spoke_balance_with_reserve c (fun _ : retainedMarkedIndex π d sample colour t J w=>d)
      ext inner hinner hdis fC reserved hcard (fun i=>(π^d) i.val) hends.2 R rfl π Subtype.val (hgeom.1 w) (hgeom.2.1 w)
  · exact marked_residual_ordinary_avoids_successors π (fun _ : retainedMarkedIndex π d sample colour t J w=>d)
      Subtype.val (outsideBufferedPathImage (fun _=>c*d) inner fC) R rfl
end Oberwolfach
