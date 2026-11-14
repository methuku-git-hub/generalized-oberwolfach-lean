module

public import Oberwolfach.PhysicalMaskChangeIncidences
public import Oberwolfach.GreedyGraphCandidates
public import Oberwolfach.MarkedBoundaryRobustSupportEvent

@[expose] public section

/-! The robust support event applies simultaneously to all later packings.
Their remaining graph determines the new physical mask; the change bound
is derived from leftover and covering degrees with the marked-head shift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]

theorem marked_boundary_mask_after_packing (tail head:E→V) (ktail khead:K→V)
    (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (X:Finset V) (Z:Finset U) (G C D:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (hG:∀ a:DirectedBoundaryEdge (markedActiveAuxTail tail ktail H₀ HK)
      (markedActiveAuxHead head khead H₀ HK) (ordinaryInnerVertices X Z),
      markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val∈G.edgeSet)
    (hCR:Disjoint C (retainedGraph G σ))
    (ℓ δ:ℝ) (hleft:∀ x,(((G\retainedGraph G σ)\C).degree x:ℝ)≤ℓ)
    (hcover:∀ x,(D.degree x:ℝ)≤δ) (x:V⊕U):
    ((Finset.univ.filter (fun a:DirectedBoundaryEdge (markedActiveAuxTail tail ktail H₀ HK)
      (markedActiveAuxHead head khead H₀ HK) (ordinaryInnerVertices X Z)=>
      (markedActiveAuxTail tail ktail H₀ HK a.val=x∨markedActiveAuxHead head khead H₀ HK a.val=x)∧
      σ (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val)≠
        decide (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val∈((G\C)\D).edgeSet))).card:ℝ)≤2*(ℓ+δ):=by
  let F:=((G\retainedGraph G σ)\C)⊔D
  have hF (v:V⊕U):(F.degree v:ℝ)≤ℓ+δ:=by
    have h: (F.degree v:ℝ)≤((G\retainedGraph G σ)\C).degree v+D.degree v:=by
      have hh:=graph_degree_sup_le ((G\retainedGraph G σ)\C) D v
      simp only [←SimpleGraph.ncard_neighborSet] at hh ⊢
      exact_mod_cast hh
    exact h.trans (add_le_add (hleft v) (hcover v))
  have hm:=marked_boundary_mask_changed_degree tail head ktail khead π H₀ HK hp X Z σ
    (fun e=>decide (e∈((G\C)\D).edgeSet)) F
    (fun a ha=>boundary_after_packing_changed_coin G C D σ hCR _ (hG a) ha) x
  have hm':((Finset.univ.filter (fun a:DirectedBoundaryEdge (markedActiveAuxTail tail ktail H₀ HK)
      (markedActiveAuxHead head khead H₀ HK) (ordinaryInnerVertices X Z)=>
      (markedActiveAuxTail tail ktail H₀ HK a.val=x∨markedActiveAuxHead head khead H₀ HK a.val=x)∧
      σ (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val)≠
        decide (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val∈((G\C)\D).edgeSet))).card:ℝ)≤
      F.degree x+F.degree ((Equiv.sumCongr π (Equiv.refl U)) x):=by
    simp only [←SimpleGraph.ncard_neighborSet] at hm ⊢
    exact_mod_cast hm
  linarith [hF x,hF ((Equiv.sumCongr π (Equiv.refl U)) x)]

end Oberwolfach
