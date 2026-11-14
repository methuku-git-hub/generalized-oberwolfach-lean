module

public import Oberwolfach.OrdinaryTraceWindowEditsFromLocalReference
public import Oberwolfach.OrdinaryRawPairStateEquality

@[expose] public section
/-! The induced level uses the original raw outcome: its sampled rim and
spokes have the trace edit bounds on that same restricted outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_trace_raw_pair_window_edits_local
    (P Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ) (i:ℕ) (Jwin:Finset ℕ)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (ρ:Equiv.Perm ↥(X i)) (hcomm:∀x:↥(X i),(ρ x).val=π x.val)
    (L:ℝ) (hbase:∀a:↥(X i)⊕↥(Z i),
      ((changed ((ordinaryPhysicalGraph ((rawWheelGraph P σ).induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>rawWheelSpokes π d σ j v.val u.val)).neighborFinset a)
        ((ordinaryPhysicalGraph (Q.induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>H v.val u.val)).neighborFinset a)).card:ℝ)≤L)
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G Hs=A)
    (hJ:∀j∈Jwin,j < i+1)
    (hX:∀j < i+1,j∉Jwin→X i⊆T j) (hZ:∀j < i+1,j∉Jwin→Z i⊆W j)
    (hXnest:∀j∈Jwin,X i⊆X j) (hZnest:∀j∈Jwin,Z i⊆Z j):
    let V₁:=↥(X i);let U₁:=↥(Z i);
    let f:V₁↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let g:U₁↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let σ₁:=ordinaryRawRestrictPair f g σ;
    let P₁:=P.induce ((X i):Set V);let G₁:=G.induce ((X i):Set V);
    let Hs₁:=fun (v:V₁) (u:U₁)=>Hs v.val u.val;
    (∀v:V₁,((changed ((rawWheelGraph P₁ σ₁).neighborFinset v) (G₁.neighborFinset v)).card:ℝ)≤L+∑j∈Jwin,cost j) ∧
    (∀v:V₁,((changed (Finset.univ.filter (rawWheelSpokes ρ d σ₁ j v)) (Finset.univ.filter (Hs₁ v))).card:ℝ)≤L+∑j∈Jwin,cost j) ∧
    (∀u:U₁,((changed (Finset.univ.filter (fun v=>rawWheelSpokes ρ d σ₁ j v u))
      (Finset.univ.filter (fun v=>Hs₁ v u))).card:ℝ)≤L+∑j∈Jwin,cost j):=by
  intro V₁ U₁ f g σ₁ P₁ G₁ Hs₁
  have hr:rawWheelGraph P₁ σ₁=(rawWheelGraph P σ).induce ((X i):Set V):=by
    exact ordinary_raw_pair_graph_eq f g P σ
  have hh:rawWheelSpokes ρ d σ₁ j=fun (v:V₁) (u:U₁)=>rawWheelSpokes π d σ j v.val u.val:=by
    convert ordinary_raw_pair_spokes_eq f g π ρ hcomm d σ j using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have he:=ordinary_trace_induced_window_edits_from_local_reference (rawWheelGraph P σ) Q (rawWheelSpokes π d σ j) H
    X T Z W cost deepCost i Jwin A G Hs L hbase htrace hstate hJ hX hZ hXnest hZnest
  rw [hr,hh]
  convert he using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
