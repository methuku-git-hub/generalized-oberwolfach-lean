module

public import Oberwolfach.LongRawRealizationsAvoidAbsorber

@[expose] public section
/-! Partial factors whose image edges lie in pairwise edge-disjoint pieces
at their own hubs have disjoint physical edge images across distinct hubs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {U A V:Type} [DecidableEq V]

def partialFactorPhysicalEdges (D:Type) (F:SimpleGraph D) (ψ:D→V):Set (Sym2 V):=
  {e | ∃x y,F.Adj x y ∧ e=s(ψ x,ψ y)}

theorem partial_factors_physical_edges_disjoint
    (D:U→Type) (F:∀u,SimpleGraph (D u)) (ψ:∀u,D u→V)
    (hub:A→U) (piece:A→Finset (Sym2 V))
    (hdis:∀a b,a≠b→Disjoint (piece a) (piece b))
    (hcover:∀u x y,(F u).Adj x y→∃a,hub a=u ∧ s(ψ u x,ψ u y)∈piece a):
    ∀u v,u≠v→Disjoint (partialFactorPhysicalEdges (D u) (F u) (ψ u))
      (partialFactorPhysicalEdges (D v) (F v) (ψ v)) :=by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨x,y,hxy,hxe⟩:=he
  obtain ⟨x',y',hxy',hxe'⟩:=he'
  obtain ⟨a,ha,hea⟩:=hcover u x y hxy
  obtain ⟨b,hb,heb⟩:=hcover v x' y' hxy'
  have hne:a≠b:=by
    intro hab
    apply huv
    exact ha.symm.trans (hab ▸ hb)
  have h₁:e∈piece a:=by rwa [hxe]
  have h₂:e∈piece b:=by rwa [hxe']
  exact (Finset.disjoint_left.mp (hdis a b hne)) h₁ h₂
end Oberwolfach
