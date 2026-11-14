module

public import Oberwolfach.OrdinaryBoundaryGraph
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
/-! After a root cover, class changes need be small only at outside roots.
For the factor host, only the root cover's restriction to the inner pair
can remove a factor edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_factor_survives_local_root_cover
    (G Gbase C D E Gpost:SimpleGraph (V⊕U)) (X:Finset V) (Z:Finset U)
    (hbase:Gbase≤spanningRestriction G (ordinaryInnerVertices X Z))
    (hC:Disjoint C (spanningRestriction G (ordinaryInnerVertices X Z)))
    (hpost:Gpost=((G\C)\D)\E):
    Gbase\(D⊔spanningRestriction E (ordinaryInnerVertices X Z))≤Gpost:=by
  intro a b hab
  have hi:=(spanningRestriction_adj _ _ _ _).mp (hbase hab.1)
  rw [hpost]
  refine ⟨⟨⟨hi.1,?_⟩,?_⟩,?_⟩
  · intro hc
    exact (disjoint_iff_inf_le.mp hC) ⟨hc,(spanningRestriction_adj _ _ _ _).mpr hi⟩
  · intro hd
    exact hab.2 (Or.inl hd)
  · intro he
    exact hab.2 (Or.inr ((spanningRestriction_adj _ _ _ _).mpr ⟨he,hi.2.1,hi.2.2⟩))

theorem ordinary_local_root_cover_class_bounds
    (B C D E R:SimpleGraph (V⊕U)) (Ω:Finset (V⊕U)) (L ell:ℝ)
    (hL:∀w,(((B\R)\C).degree w:ℝ)+(D.degree w:ℝ)≤L)
    (hE:∀w∉Ω,(E.degree w:ℝ)≤ell):
    ∀w∉Ω,(((B\R)\C).degree w:ℝ)+((D⊔E).degree w:ℝ)≤L+ell:=by
  intro w hw
  have hd:=graph_degree_sup_le D E w
  have hdR:((D⊔E).degree w:ℝ)≤(D.degree w:ℝ)+(E.degree w:ℝ):=by exact_mod_cast hd
  linarith only [hL w,hE w hw,hdR]
end Oberwolfach
