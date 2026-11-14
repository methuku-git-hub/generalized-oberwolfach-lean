module

public import Oberwolfach.BoundaryDegreeAfterPacking
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! A further root-cover deletion cannot increase the degree of the already
controlled sampled boundary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_boundary_degree
    (Q₀ Q':SimpleGraph V) (H₀ H':V→U→Prop) (X:Finset V) (Z:Finset U)
    (C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool) (p ε L ρ:ℝ) (Dmax:ℕ)
    (hp:0≤p) (hsample:BoundaryReserveSupportGood (ordinaryBoundaryGraph Q₀ H₀ X Z) p ε σ)
    (hCR:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ))
    (hL:∀w,((((ordinaryBoundaryGraph Q₀ H₀ X Z)\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)+(D.degree w:ℝ)≤L)
    (hsub:ordinaryBoundaryGraph Q' H' X Z≤((ordinaryBoundaryGraph Q₀ H₀ X Z\C)\D))
    (hdeg:(p+ε)*Fintype.card (V⊕U)+L≤ρ*Fintype.card (V⊕U))
    (hDmax:ρ*Fintype.card (V⊕U)≤(Dmax:ℝ)):
    ∀w:V⊕U,(ordinaryBoundaryGraph Q' H' X Z).degree w≤Dmax:=by
  have hbd:=boundary_degree_after_packing (ordinaryBoundaryGraph Q₀ H₀ X Z) C D σ p ε L hp hsample hCR hL
  intro w
  have hd:((ordinaryBoundaryGraph Q' H' X Z).degree w:ℝ)≤
      ((((ordinaryBoundaryGraph Q₀ H₀ X Z)\C)\D).degree w:ℝ):=by
    exact_mod_cast SimpleGraph.degree_le_of_le hsub
  exact_mod_cast hd.trans ((hbd w).trans (hdeg.trans hDmax))
end Oberwolfach
