module

public import Oberwolfach.LongResidualRimComplementAvoidance
public import Oberwolfach.MarkedPhysicalHostContainment

@[expose] public section
/-! Physical rims from the same eligible directed residual avoid all of the
already embedded buffered complements, including marked rims. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_marked_rim_complement_avoidance
    {V U E K:Type} {X:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)] [Fintype V] [LinearOrder V] [Nonempty V] [Fintype E] [Fintype K]
    (M:V→V→ℕ) (Small:SimpleGraph V)
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hE:∀e,longEligibleResidualArc M Small ⊥ (tail e,head e))
    (hK:∀e,longEligibleResidualArc M Small ⊥ (ktail e,π (khead e)))
    (F:∀u,SimpleGraph (X u)) (f:∀u,X u→V)
    (hPacked:∀u,((F u).edgeFinset.image (Sym2.map (f u)))⊆Small.edgeFinset):
    ∀u x y,(F u).Adj x y→
      ({f u x,f u y}:Finset V)∉markedPhysicalRimSet tail head ktail khead π:=by
  intro u x y hxy hmem
  have he:s(f u x,f u y)∈Small.edgeFinset:=hPacked u (Finset.mem_image.mpr
    ⟨s(x,y),SimpleGraph.mem_edgeFinset.mpr hxy,rfl⟩)
  have hs:Small.Adj (f u x) (f u y):=SimpleGraph.mem_edgeFinset.mp he
  obtain ⟨e,_,heq⟩:=Finset.mem_image.mp hmem
  cases e with
  | inl e =>
    let B:Finset (V×V):={(tail e,head e)}
    have hb:∀a∈B,longEligibleResidualArc M Small ⊥ a:=by
      intro a ha
      have : a=(tail e,head e):=Finset.mem_singleton.mp ha
      subst a
      exact hE e
    apply long_eligible_rim_avoids_small M Small B hb (f u x) (f u y) ?_ hs
    apply Finset.mem_image.mpr
    refine ⟨(tail e,head e),Finset.mem_singleton_self _,?_⟩
    simpa only [markedPhysicalEdge,Sum.elim_inl] using heq
  | inr e =>
    let B:Finset (V×V):={(ktail e,π (khead e))}
    have hb:∀a∈B,longEligibleResidualArc M Small ⊥ a:=by
      intro a ha
      have : a=(ktail e,π (khead e)):=Finset.mem_singleton.mp ha
      subst a
      exact hK e
    apply long_eligible_rim_avoids_small M Small B hb (f u x) (f u y) ?_ hs
    apply Finset.mem_image.mpr
    refine ⟨(ktail e,π (khead e)),Finset.mem_singleton_self _,?_⟩
    simpa only [markedPhysicalEdge,Sum.elim_inr] using heq
end Oberwolfach
