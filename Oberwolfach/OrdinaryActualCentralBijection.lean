module

public import Oberwolfach.OrdinaryActualCentralMaps

@[expose] public section

/-! The finite expansion-to-central resource bijection before embedding.
The map may identify old vertices and hubs but never distinct physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ E J W:Type} [Fintype V₀] [Fintype U₀] [Fintype E] [Fintype J] [Fintype W]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq E] [DecidableEq J] [DecidableEq W]

theorem actual_finite_expansion_central_bijection (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop)
    (C:SimpleGraph W) (z o:W) (hzo:z≠o) (e:G.edgeFinset≃E) (j:ActualSpoke Hs≃J) :
    let source:=ordinaryHostResources (actualExpansionRim G Hs C z o) (actualExpansionSpokes G Hs z)
    let target:=ordinaryHostResources (ordinaryExpansionRim (J:=J) C z o (fun _:E=>()) (fun _=>()))
      (ordinaryExpansionSpokes (E:=E) z (fun _:J=>()) (fun _=>()))
    let f:=ordinaryPairResourceMap (actualCentralRowMap (W:=W) G Hs e j) (actualCentralHubMap G Hs e j)
    Set.InjOn f source∧source.image f=target := by
  dsimp only
  have hmaps:ordinaryPairResourceMap (actualCentralRowMap (W:=W) G Hs e j) (actualCentralHubMap G Hs e j)=
      expansionReindexResource (V:=Unit) (U:=Unit) (W:=W) e j ∘
        expansionResourceMap (E:=G.edgeFinset) (J:=ActualSpoke Hs) (W:=W) (fun _:V₀=>()) (fun _:U₀=>()) := by
    funext a
    cases a with
    | inl a=>induction a using Sym2.ind with | _ v w=>rfl
    | inr p=>rfl
  rw [hmaps]
  exact ordinaryExpansion_common_central_resources C z o hzo
    (fun e:G.edgeFinset=>e.val.out.1) (fun e:G.edgeFinset=>e.val.out.2)
    (fun j:ActualSpoke Hs=>j.val.1) (fun j:ActualSpoke Hs=>j.val.2) e j

end Oberwolfach
