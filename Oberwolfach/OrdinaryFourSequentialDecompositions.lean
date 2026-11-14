module

public import Oberwolfach.OrdinarySequentialHostDecompositions
public import Oberwolfach.OrdinarySequentialWheelDecompositions

@[expose] public section
/-! Four successive wheel decompositions combine in the original host,
with their exact final remainder and physical edge disjointness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_four_sequential_decompositions
    (Q A B C D F:SimpleGraph V) (H SA SB SC SD:V→U→Prop) (r:ℕ)
    (hA:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources A SA))
    (hB:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources B SB))
    (hC:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources C SC))
    (hD:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources D SD))
    (hdecA:HasOrdinaryWheelDecomposition A SA r) (hdecB:HasOrdinaryWheelDecomposition B SB r)
    (hdecC:HasOrdinaryWheelDecomposition C SC r) (hdecD:HasOrdinaryWheelDecomposition D SD r)
    (hBsub:B≤Q\A) (hSB:∀v u,SB v u→H v u∧¬SA v u)
    (hCsub:C≤(Q\A)\B) (hSC:∀v u,SC v u→(H v u∧¬SA v u)∧¬SB v u)
    (hDsub:D≤((Q\A)\B)\C) (hSD:∀v u,SD v u→((H v u∧¬SA v u)∧¬SB v u)∧¬SC v u):
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources (((A⊔B)⊔C)⊔D) (fun v u=>((SA v u∨SB v u)∨SC v u)∨SD v u)) ∧
    HasOrdinaryWheelDecomposition (((A⊔B)⊔C)⊔D) (fun v u=>((SA v u∨SB v u)∨SC v u)∨SD v u) r ∧
    Q\(((A⊔B)⊔C)⊔D)=(((Q\A)\B)\C)\D ∧
    (fun v u=>H v u∧¬(((SA v u∨SB v u)∨SC v u)∨SD v u))=
      (fun v u=>(((H v u∧¬SA v u)∧¬SB v u)∧¬SC v u)∧¬SD v u):=by
  let R:=((A⊔B)⊔C)
  let S:=fun v u=>(SA v u∨SB v u)∨SC v u
  have hthree:=ordinary_sequential_wheel_decompositions Q A B C H SA SB SC r hBsub hCsub hSB hSC hdecA hdecB hdecC
  have hhost:=ordinary_sequential_host_decompositions Q A B C F H SA SB SC r hA hB hC hBsub hSB hCsub hSC
  have hRD:Disjoint R D:=by
    apply disjoint_iff_inf_le.mpr
    intro v w h
    have hd:=hDsub h.2
    rcases h.1 with (ha|hb)|hc
    · exact hd.1.1.2 ha
    · exact hd.1.2 hb
    · exact hd.2 hc
  have hSDdis:∀v u,¬(S v u∧SD v u):=by
    intro v u h
    have hd:=hSD v u h.2
    rcases h.1 with (ha|hb)|hc
    · exact hd.1.1.2 ha
    · exact hd.1.2 hb
    · exact hd.2 hc
  have hresdis:=ordinaryHostResources_disjoint R D S SD hRD hSDdis
  have hboth:=resource_decomposition_union _ _ _ hhost hD hresdis
  rw [←ordinaryHostResources_union] at hboth
  have hdec:=ordinary_wheel_decomposition_union R D S SD r hthree.1 hdecD hRD hSDdis
  refine ⟨hboth,hdec,?_,?_⟩
  · ext v w
    simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj]
    tauto
  · funext v u
    apply propext
    tauto
end Oberwolfach
