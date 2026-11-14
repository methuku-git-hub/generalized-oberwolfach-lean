module

public import Oberwolfach.OrdinaryRootStarBoundaryZero
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
/-! At a deeper boundary inside the current pair, the approximate packing
contributes nothing, the final root-free wheels contribute nothing, and the
only possible losses are the cleanup and the small inner correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_boundary_four_pieces
    (Q A B C D:SimpleGraph V) (H SA SB SC SD:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (ν η:ℝ)
    (hAsub:ordinaryPhysicalGraph A SA≤ordinaryPhysicalGraph Q H)
    (hA:Disjoint (ordinaryPhysicalGraph A SA) (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)))
    (hB:∀w:V⊕U,((ordinaryPhysicalGraph B SB).degree w:ℝ)≤ν)
    (hC:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph C SC) (ordinaryInnerVertices X Z)).degree w:ℝ)≤η)
    (hD:Disjoint (ordinaryPhysicalGraph D SD) (ordinaryDeepRootStar T W)):
    ∀w:V⊕U,((spanningRestriction
      (ordinaryBoundaryGraph (((A⊔B)⊔C)⊔D) (fun v u=>((SA v u∨SB v u)∨SC v u)∨SD v u) T W)
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤ν+η:=by
  let Ω:=ordinaryInnerVertices X Z
  let G:=ordinaryPhysicalGraph (((A⊔B)⊔C)⊔D) (fun v u=>((SA v u∨SB v u)∨SC v u)∨SD v u)
  let I:=spanningRestriction (ordinaryBoundaryGraph (((A⊔B)⊔C)⊔D)
    (fun v u=>((SA v u∨SB v u)∨SC v u)∨SD v u) T W) Ω
  have hphys:G=((ordinaryPhysicalGraph A SA⊔ordinaryPhysicalGraph B SB)⊔ordinaryPhysicalGraph C SC)⊔ordinaryPhysicalGraph D SD:=by
    ext a b
    cases a <;> cases b <;> simp [G,ordinaryPhysicalGraph]
  have hsub:I≤ordinaryPhysicalGraph B SB⊔spanningRestriction (ordinaryPhysicalGraph C SC) Ω:=by
    intro a b hab
    have hi:=(spanningRestriction_adj _ _ _ _).mp hab
    have hb:=(ordinaryBoundaryGraph_adj _ _ _ _ _ _).mp hi.1
    have hroot:a∈ordinaryInnerVertices T W∨b∈ordinaryInnerVertices T W:=by
      rcases hb.2 with h|h
      · exact Or.inr h.2
      · exact Or.inl h.2
    have he:G.Adj a b:=hb.1
    rw [hphys] at he
    rcases he with ((ha|hb')|hc)|hd
    · have hinner:(spanningRestriction (ordinaryPhysicalGraph Q H) Ω).Adj a b:=
        (spanningRestriction_adj _ _ _ _).mpr ⟨hAsub ha,hi.2.1,hi.2.2⟩
      exact ((disjoint_iff_inf_le.mp hA) ⟨ha,hinner⟩).elim
    · exact Or.inl hb'
    · exact Or.inr ((spanningRestriction_adj _ _ _ _).mpr ⟨hc,hi.2.1,hi.2.2⟩)
    · have hstar:=ordinary_edge_touching_deep_root_star D SD T W a b hd hroot
      exact ((disjoint_iff_inf_le.mp hD) ⟨hd,hstar⟩).elim
  intro w
  have hd:((I.degree w):ℝ)≤((ordinaryPhysicalGraph B SB).degree w:ℝ)+
      ((spanningRestriction (ordinaryPhysicalGraph C SC) Ω).degree w:ℝ):=by
    have hn: I.degree w≤(ordinaryPhysicalGraph B SB).degree w+
        (spanningRestriction (ordinaryPhysicalGraph C SC) Ω).degree w:=
      (SimpleGraph.degree_le_of_le hsub).trans (graph_degree_sup_le _ _ w)
    exact_mod_cast hn
  exact hd.trans (add_le_add (hB w) (hC w))
end Oberwolfach
