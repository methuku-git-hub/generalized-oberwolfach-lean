module

public import Oberwolfach.OrdinaryMatchedPhysicalHubFamilyShape

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matched_physical_hub_family_named
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (R:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    OrdinaryMatchedPhysicalHubFamilyShape (K:=K) π d m R H :=by
  unfold OrdinaryMatchedPhysicalHubFamilyShape
  intro RM state RR φ L hL AM AU len Q E S MW W Good Pack X A B _ _ _ _ _ _ G root Arc Avail Reserve Pos hsource Host hArc
  have hpack:∀w:∀u,W u,(∀u,Good u (w u))→∀u v,u≠v→Disjoint (Pack u (w u)) (Pack v (w v)):=by
    intro w hw u v huv
    exact ordinary_physical_pair_hub_rim_packs_named (K:=K) π d m R H L hL u v huv (w u) (w v) (hw u) (hw v)
  exact ordinary_matched_residual_hub_family G m d π root Arc Avail Reserve Good Pack Pos len hsource hpack Host hArc
end Oberwolfach
