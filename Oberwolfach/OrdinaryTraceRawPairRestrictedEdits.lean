module

public import Oberwolfach.OrdinaryTraceRawPairEditsLocal
public import Oberwolfach.OrdinaryTypedChangesRestrict

@[expose] public section
/-! Restrict the actual protected-trace edit bounds to any fixed subdomain
of the current parent, using the same raw outcome and local permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color V₂ U₂:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Fintype V₂] [Fintype U₂] [LinearOrder V] [LinearOrder V₂] [DecidableEq U] [DecidableEq U₂]

theorem ordinary_trace_raw_pair_restricted_edits
    (P Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ) (i:ℕ)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (ρ:Equiv.Perm ↥(X i)) (hcomm:∀x:↥(X i),(ρ x).val=π x.val)
    (L:ℝ) (hbase:∀a:↥(X i)⊕↥(Z i),
      ((changed ((ordinaryPhysicalGraph ((rawWheelGraph P σ).induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>rawWheelSpokes π d σ j v.val u.val)).neighborFinset a)
        ((ordinaryPhysicalGraph (Q.induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>H v.val u.val)).neighborFinset a)).card:ℝ)≤L)
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G Hs=A) (hX:∀j < i,X i⊆T j) (hZ:∀j < i,Z i⊆W j)
    (f₂:V₂↪↥(X i)) (g₂:U₂↪↥(Z i)) (ρ₂:Equiv.Perm V₂)
    (hcomm₂:∀x,f₂ (ρ₂ x)=ρ (f₂ x)):
    let V₁:=↥(X i);let U₁:=↥(Z i)
    let f₁:V₁↪V:=⟨Subtype.val,Subtype.val_injective⟩
    let g₁:U₁↪U:=⟨Subtype.val,Subtype.val_injective⟩
    let σ₁:=ordinaryRawRestrictPair f₁ g₁ σ
    let σ₂:=ordinaryRawRestrictPair f₂ g₂ σ₁
    let P₁:=P.induce ((X i):Set V);let G₁:=G.induce ((X i):Set V)
    let P₂:=P₁.comap f₂;let G₂:=G₁.comap f₂
    let H₂:=fun (v:V₂) (u:U₂)=>Hs (f₁ (f₂ v)) (g₁ (g₂ u));
    (∀v:V₂,((changed ((rawWheelGraph P₂ σ₂).neighborFinset v) (G₂.neighborFinset v)).card:ℝ)≤L+cost i) ∧
    (∀v:V₂,((changed (Finset.univ.filter (rawWheelSpokes ρ₂ d σ₂ j v)) (Finset.univ.filter (H₂ v))).card:ℝ)≤L+cost i) ∧
    (∀u:U₂,((changed (Finset.univ.filter (fun v=>rawWheelSpokes ρ₂ d σ₂ j v u))
      (Finset.univ.filter (fun v=>H₂ v u))).card:ℝ)≤L+cost i) :=by
  intro V₁ U₁ f₁ g₁ σ₁ σ₂ P₁ G₁ P₂ G₂ H₂
  have hparent:=ordinary_trace_raw_pair_edits_local P Q H π d j σ X T Z W cost deepCost i A G Hs ρ hcomm L hbase htrace hstate hX hZ
  have hrestrict:=ordinary_typed_changes_restrict (rawWheelGraph P₁ σ₁) G₁ (rawWheelSpokes ρ d σ₁ j)
    (fun (v:V₁) (u:U₁)=>Hs (f₁ v) (g₁ u)) f₂ g₂ (L+cost i) hparent.1 hparent.2.1 hparent.2.2
  have hgraph:rawWheelGraph P₂ σ₂=(rawWheelGraph P₁ σ₁).comap f₂:=ordinary_raw_pair_graph_eq f₂ g₂ P₁ σ₁
  have hspoke:rawWheelSpokes ρ₂ d σ₂ j=fun v u=>rawWheelSpokes ρ d σ₁ j (f₂ v) (g₂ u):=by
    convert ordinary_raw_pair_spokes_eq f₂ g₂ ρ ρ₂ hcomm₂ d σ₁ j using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  rw [hgraph,hspoke]
  exact hrestrict
end Oberwolfach
