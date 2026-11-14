module

public import Oberwolfach.OrdinaryMappedProtectedCosts
public import Oberwolfach.OrdinaryInducedProtectedRemainder
public import Oberwolfach.OrdinaryHostDecomposedRemainder
public import Oberwolfach.OrdinaryHostDecompositionEmbedding

@[expose] public section
/-! A protected wheel cover-down on an induced pair lifts to the actual
ambient host, preserving balance, both costs and deeper-pair avoidance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_protected_coverdown
    (Q F:SimpleGraph V) (H:V→U→Prop) (Y:Finset V) (B:Finset U)
    (X T:Finset ↥Y) (Z W:Finset ↥B) (r:ℕ) (cost deepCost:ℝ) (hc0:0≤cost) (hd0:0≤deepCost)
    (hparent:ordinaryHostResources Q H⊆ordinaryRootResources Y B)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card):
    let φ:↥Y↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:↥B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    OrdinaryProtectedHostCoverDownResult (Q.induce (Y:Set V)) (F.induce (Y:Set V))
      (fun (v:↥Y) (u:↥B)=>H v.val u.val) X T Z W r cost deepCost→
    OrdinaryProtectedHostCoverDownResult Q F H (X.image φ) (T.image φ) (Z.image ψ) (W.image ψ) r cost deepCost:=by
  intro φ ψ hstep
  obtain ⟨D,E,hD,hE,hdec,hroot,hbl,hdl,hcost,hdeep,havoid⟩:=hstep
  let D':=D.map φ
  let E':=ordinaryMappedSpokes E φ ψ
  have hhost:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources D' E'):=by
    apply ordinary_host_decomposition_embedding (Q.induce (Y:Set V)) (F.induce (Y:Set V)) D
      (fun (v:↥Y) (u:↥B)=>H v.val u.val) E Q F H r φ ψ
    · intro v w hvw
      exact hvw
    · intro v u h
      exact h
    · intro v w h
      exact h
    · exact hdec
  have hforget:HasOrdinaryWheelDecomposition D' E' r:=ordinary_host_decomposition_forget (ordinaryHostResources D' E') hhost
  have hremain:=ordinary_host_decomposed_remainder Q D' F H E' r hhost hforget hbal hdiv
  have hroot':ordinaryHostResources (Q\D') (fun v u=>H v u∧¬E' v u)⊆
      ordinaryRootResources (X.image φ) (Z.image ψ):=by
    exact ordinary_induced_protected_remainder_roots Q H Y B D E X Z hparent hroot
  have hc:=ordinary_mapped_protected_costs D E X T Z W φ ψ cost deepCost hc0 hd0 hcost hdeep havoid
  exact ⟨D',E',hremain.1,hremain.2.1,hhost,hroot',hremain.2.2.1,hremain.2.2.2,hc.1,hc.2.1,hc.2.2⟩
end Oberwolfach
