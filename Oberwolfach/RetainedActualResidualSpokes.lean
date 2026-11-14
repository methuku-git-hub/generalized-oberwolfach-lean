module

public import Oberwolfach.ActualOutsidePathAvoidance
public import Oberwolfach.RetainedMarkedMatchingInputs
public import Oberwolfach.MarkedVariableResidualSpokeBalance

@[expose] public section
/-! The retained marked roots lie in the residual spokes using avoidance only
on the source vertices outside the final paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V U Γ Color Kbad Jbad:Type} [Fintype X] [DecidableEq X]
  [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
  [DecidableEq Kbad] [DecidableEq Jbad]

theorem retained_actual_residual_spoke_identities
    (π:Equiv.Perm V) (c d:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (sample:RawIntervalFamilyOutcome V U Γ Color) (colour:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d sample colour) t) (w:U)
    (F:SimpleGraph X) (data:ActualResidualData (K:=Kbad) (J:=Jbad) F)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (ext:∀i:retainedMarkedIndex π d sample colour t J w,Fin (c*d+5)↪X)
    (inner:∀i:retainedMarkedIndex π d sample colour t J w,Fin (c*d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (fC:{x // x∉bufferedPathStrictInterior (fun _=>c*d) inner}↪V)
    (hcard:Fintype.card X=Fintype.card V)
    (hend:∀i,fC (bufferedEndpointInComplement (fun _=>c*d) ext inner hinner hdis i)=(π^d) i.val)
    (ψ:X→V) (Φ g:{x // x∈data.remaining}→V)
    (Anchors:Finset {x // x∈data.remaining}) (Lists:Finset V)
    (hold:∀(x:{x // x∉bufferedPathStrictInterior (fun _=>c*d) inner}),
      x.val∈data.oldDomain→fC x=ψ x.val)
    (hnew:∀(x:{x // x∉bufferedPathStrictInterior (fun _=>c*d) inner}) (hx:x.val∈data.remaining),
      fC x=Φ ⟨x.val,hx⟩)
    (hAnchor:∀x∈Anchors,Φ x=g x) (hFree:∀x,x∉Anchors→Φ x∈Lists):
    let Y:=markedIntervalRootSet π (fun _ : retainedMarkedIndex π d sample colour t J w=>d) Subtype.val
    let B:=Finset.univ.image (fun i:retainedMarkedIndex π d sample colour t J w=>(π^d) i.val)
    let Z:=outsideBufferedPathImage (fun _=>c*d) inner fC
    let R:=Finset.univ\(Z∪B)
    (∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>c*d) inner→ψ x∉Y)→
    (∀x∈Anchors,x.val∉bufferedPathFullDomain (fun _=>c*d) inner → g x∉Y)→
    Disjoint Lists Y→
    Y⊆R ∧ R.card=c*Y.card ∧ Disjoint (R\Y) (Y.image π):=by
  intro Y B Z R hOldAvoid hAnchorAvoid hListAvoid
  have hgeom:=retained_marked_interval_geometry π d (by omega) hnoshort sample colour t J
  have havoid:Disjoint Z Y:=actual_outside_buffered_path_image_avoids_reserved F data hCycle
    (fun _=>c*d) inner fC ψ Φ g Anchors Lists Y hold hnew hAnchor hFree hOldAvoid hAnchorAvoid hListAvoid
  refine ⟨?_,?_,?_⟩
  · exact marked_interval_roots_in_residual π (fun _ : retainedMarkedIndex π d sample colour t J w=>d) Subtype.val
      (hgeom.1 w) (hgeom.2.1 w) Z R havoid.symm rfl
  · exact marked_variable_residual_spoke_balance c (fun _ : retainedMarkedIndex π d sample colour t J w=>d)
      ext inner hinner hdis fC hcard (fun i=>(π^d) i.val) hend R rfl π Subtype.val (hgeom.1 w) (hgeom.2.1 w)
  · exact marked_residual_ordinary_avoids_successors π (fun _ : retainedMarkedIndex π d sample colour t J w=>d)
      Subtype.val Z R rfl
end Oberwolfach
