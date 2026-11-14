module

public import Oberwolfach.OrdinaryDeepBlocker
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
/-! The deep blocker is supported inside the enclosing pair.  Thus any
subgraph of the host that avoids the enclosing pair also avoids this blocker. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_blocker_support_nested (X T:Finset V) (Z W:Finset U)
    (hTX:T⊆X) (hWZ:W⊆Z) (a b:V⊕U) (hab:(ordinaryDeepBlocker T W).Adj a b):
    a∈ordinaryInnerVertices X Z ∧ b∈ordinaryInnerVertices X Z:=by
  cases a with
  | inl v=>cases b with
    | inl w=>
      have h:=(ordinary_deep_rim_blocker_adj T v w).mp hab
      exact ⟨(ordinaryInnerVertices_left X Z v).mpr (hTX h.2.1),
        (ordinaryInnerVertices_left X Z w).mpr (hTX h.2.2)⟩
    | inr u=>
      exact ⟨(ordinaryInnerVertices_left X Z v).mpr (hTX hab.1),
        (ordinaryInnerVertices_right X Z u).mpr (hWZ hab.2)⟩
  | inr u=>cases b with
    | inl v=>
      exact ⟨(ordinaryInnerVertices_right X Z u).mpr (hWZ hab.2),
        (ordinaryInnerVertices_left X Z v).mpr (hTX hab.1)⟩
    | inr z=>exact hab.elim

theorem ordinary_avoids_nested_deep_blocker (G C:SimpleGraph (V⊕U))
    (X T:Finset V) (Z W:Finset U) (hTX:T⊆X) (hWZ:W⊆Z)
    (hsub:C≤G) (havoid:Disjoint C (spanningRestriction G (ordinaryInnerVertices X Z))):
    Disjoint C (ordinaryDeepBlocker T W):=by
  apply disjoint_iff_inf_le.mpr
  intro a b hab
  obtain ⟨ha,hb⟩:=ordinary_deep_blocker_support_nested X T Z W hTX hWZ a b hab.2
  exact (disjoint_iff_inf_le.mp havoid) ⟨hab.1,(spanningRestriction_adj _ _ _ _).mpr ⟨hsub hab.1,ha,hb⟩⟩

theorem ordinary_deep_blocker_union_degree (D:SimpleGraph (V⊕U)) (T:Finset V) (W:Finset U)
    (δ:ℝ) (hD:∀w,(D.degree w:ℝ)≤δ) (w:V⊕U):
    (((D⊔ordinaryDeepBlocker T W).degree w):ℝ)≤δ+T.card+W.card:=by
  have hd:=graph_degree_sup_le D (ordinaryDeepBlocker T W) w
  have hdR:(((D⊔ordinaryDeepBlocker T W).degree w):ℝ)≤
      (D.degree w:ℝ)+((ordinaryDeepBlocker T W).degree w:ℝ):=by exact_mod_cast hd
  have hb:=ordinary_deep_blocker_degree T W w
  linarith only [hdR,hD w,hb]
end Oberwolfach
