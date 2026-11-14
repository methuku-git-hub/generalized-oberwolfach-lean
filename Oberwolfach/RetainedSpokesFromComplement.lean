module

public import Oberwolfach.RetainedActualResidualSpokes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_spoke_identities_from_complement
    {X V U Γ Color:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (π:Equiv.Perm V) (c d:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (sample:RawIntervalFamilyOutcome V U Γ Color) (colour:Γ) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d sample colour) t) (w:U)
    (ext:∀i:retainedMarkedIndex π d sample colour t J w,Fin (c*d+5)↪X)
    (inner:∀i:retainedMarkedIndex π d sample colour t J w,Fin (c*d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (fC:{x // x∉bufferedPathStrictInterior (fun _=>c*d) inner}↪V)
    (hcard:Fintype.card X=Fintype.card V)
    (hend:∀i,fC (bufferedEndpointInComplement (fun _=>c*d) ext inner hinner hdis i)=(π^d) i.val):
    let Y:=markedIntervalRootSet π (fun _ : retainedMarkedIndex π d sample colour t J w=>d) Subtype.val
    let B:=Finset.univ.image (fun i:retainedMarkedIndex π d sample colour t J w=>(π^d) i.val)
    let Z:=outsideBufferedPathImage (fun _=>c*d) inner fC
    let R:=Finset.univ\(Z∪B)
    Disjoint Z Y → Y⊆R ∧ R.card=c*Y.card ∧ Disjoint (R\Y) (Y.image π):=by
  intro Y B Z R havoid
  have hgeom:=retained_marked_interval_geometry π d (by omega) hnoshort sample colour t J
  refine ⟨?_,?_,?_⟩
  · exact marked_interval_roots_in_residual π (fun _ : retainedMarkedIndex π d sample colour t J w=>d) Subtype.val
      (hgeom.1 w) (hgeom.2.1 w) Z R havoid.symm rfl
  · exact marked_variable_residual_spoke_balance c (fun _ : retainedMarkedIndex π d sample colour t J w=>d)
      ext inner hinner hdis fC hcard (fun i=>(π^d) i.val) hend R rfl π Subtype.val (hgeom.1 w) (hgeom.2.1 w)
  · exact marked_residual_ordinary_avoids_successors π (fun _ : retainedMarkedIndex π d sample colour t J w=>d)
      Subtype.val Z R rfl
end Oberwolfach
