module

public import Oberwolfach.LongComplementImageInSmall
public import Oberwolfach.LongMarkedRimComplementAvoidance

@[expose] public section
/-! The complement arc split and eligible residual rims imply the exact rim
avoidance required by the buffered factor reconstruction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_marked_rim_from_complement_arc_split
    {U V E K:Type} [Fintype U] [DecidableEq U] [Fintype V] [LinearOrder V] [Nonempty V]
    [Fintype E] [Fintype K] {X:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (F:∀u,SimpleGraph (X u)) (f:∀u,X u→V)
    (arcs:U→Finset (V×V)) (A:Finset (V×V)) (Small:SimpleGraph V)
    (hA:A=Finset.univ.biUnion arcs)
    (hSmall:Small.edgeFinset=A.image (fun a=>s(a.1,a.2)))
    (hExact:∀u,((F u).edgeFinset.image (Sym2.map (f u)))=
      (arcs u).image (fun a=>s(a.1,a.2)))
    (M:V→V→ℕ) (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hE:∀e,longEligibleResidualArc M Small ⊥ (tail e,head e))
    (hK:∀e,longEligibleResidualArc M Small ⊥ (ktail e,π (khead e))):
    ∀u x y,(F u).Adj x y→
      ({f u x,f u y}:Finset V)∉markedPhysicalRimSet tail head ktail khead π:=by
  apply long_marked_rim_complement_avoidance M Small tail head ktail khead π hE hK F f
  exact long_complement_image_in_small F f arcs A Small hA hSmall hExact
end Oberwolfach
