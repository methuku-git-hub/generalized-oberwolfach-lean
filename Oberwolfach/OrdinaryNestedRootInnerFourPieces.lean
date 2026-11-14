module

public import Oberwolfach.OrdinaryRootStarBoundaryZero
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
/-! If the finishing wheels avoid an intermediate root star, their cost
inside every pair nested in it vanishes. The packing also contributes zero;
only the cover and cleanup remain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nested_root_inner_four_pieces
    (Q A B C D:SimpleGraph V) (H SA SB SC SD:V→U→Prop)
    (X T Tplus:Finset V) (Z W Wplus:Finset U) (ν η:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z) (hTT:T⊆Tplus) (hWW:W⊆Wplus)
    (hAsub:ordinaryPhysicalGraph A SA≤ordinaryPhysicalGraph Q H)
    (hA:Disjoint (ordinaryPhysicalGraph A SA) (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)))
    (hB:∀w:V⊕U,((ordinaryPhysicalGraph B SB).degree w:ℝ)≤ν)
    (hC:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph C SC) (ordinaryInnerVertices X Z)).degree w:ℝ)≤η)
    (hD:Disjoint (ordinaryPhysicalGraph D SD) (ordinaryDeepRootStar Tplus Wplus)):
    ∀w:V⊕U,((spanningRestriction
      (ordinaryPhysicalGraph (((A⊔B)⊔C)⊔D) (fun v u=>((SA v u∨SB v u)∨SC v u)∨SD v u))
      (ordinaryInnerVertices T W)).degree w:ℝ)≤ν+η:=by
  let Ω:=ordinaryInnerVertices X Z
  let Θ:=ordinaryInnerVertices T W
  let G:=ordinaryPhysicalGraph (((A⊔B)⊔C)⊔D) (fun v u=>((SA v u∨SB v u)∨SC v u)∨SD v u)
  let I:=spanningRestriction G Θ
  have hΩ:Θ⊆Ω:=by
    intro a ha
    cases a with
    | inl v=>exact (ordinaryInnerVertices_left X Z v).mpr (hTX ((ordinaryInnerVertices_left T W v).mp ha))
    | inr u=>exact (ordinaryInnerVertices_right X Z u).mpr (hWZ ((ordinaryInnerVertices_right T W u).mp ha))
  have hroot:Θ⊆ordinaryInnerVertices Tplus Wplus:=by
    intro a ha
    cases a with
    | inl v=>exact (ordinaryInnerVertices_left Tplus Wplus v).mpr (hTT ((ordinaryInnerVertices_left T W v).mp ha))
    | inr u=>exact (ordinaryInnerVertices_right Tplus Wplus u).mpr (hWW ((ordinaryInnerVertices_right T W u).mp ha))
  have hphys:G=((ordinaryPhysicalGraph A SA⊔ordinaryPhysicalGraph B SB)⊔ordinaryPhysicalGraph C SC)⊔ordinaryPhysicalGraph D SD:=by
    ext a b
    cases a <;> cases b <;> simp [G,ordinaryPhysicalGraph]
  have hsub:I≤ordinaryPhysicalGraph B SB⊔spanningRestriction (ordinaryPhysicalGraph C SC) Ω:=by
    intro a b hab
    have hi:=(spanningRestriction_adj _ _ _ _).mp hab
    have he:G.Adj a b:=hi.1
    rw [hphys] at he
    rcases he with ((ha|hb)|hc)|hd
    · have hinner:(spanningRestriction (ordinaryPhysicalGraph Q H) Ω).Adj a b:=
        (spanningRestriction_adj _ _ _ _).mpr ⟨hAsub ha,hΩ hi.2.1,hΩ hi.2.2⟩
      exact ((disjoint_iff_inf_le.mp hA) ⟨ha,hinner⟩).elim
    · exact Or.inl hb
    · exact Or.inr ((spanningRestriction_adj _ _ _ _).mpr ⟨hc,hΩ hi.2.1,hΩ hi.2.2⟩)
    · have hs:=ordinary_edge_touching_deep_root_star D SD Tplus Wplus a b hd (Or.inl (hroot hi.2.1))
      exact ((disjoint_iff_inf_le.mp hD) ⟨hd,hs⟩).elim
  intro w
  have hd:((I.degree w):ℝ)≤((ordinaryPhysicalGraph B SB).degree w:ℝ)+
      ((spanningRestriction (ordinaryPhysicalGraph C SC) Ω).degree w:ℝ):=by
    have hn:I.degree w≤(ordinaryPhysicalGraph B SB).degree w+
        (spanningRestriction (ordinaryPhysicalGraph C SC) Ω).degree w:=
      (SimpleGraph.degree_le_of_le hsub).trans (graph_degree_sup_le _ _ w)
    exact_mod_cast hn
  exact hd.trans (add_le_add (hB w) (hC w))
end Oberwolfach
