module

public import Oberwolfach.OrdinaryProtectedHostCoverDownResult
public import Oberwolfach.OrdinaryGraphPairEmbeddings

@[expose] public section
/-! If the current host is supported on an enclosing pair, a cover-down of
its induced host leaves the actual ambient remainder on the mapped roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_protected_remainder_roots
    (Q:SimpleGraph V) (H:V→U→Prop) (Y:Finset V) (B:Finset U)
    (D:SimpleGraph ↥Y) (E:↥Y→↥B→Prop) (X:Finset ↥Y) (Z:Finset ↥B)
    (hparent:ordinaryHostResources Q H⊆ordinaryRootResources Y B):
    let φ:↥Y↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:↥B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    ordinaryHostResources ((Q.induce (Y:Set V))\D)
      (fun (v:↥Y) (u:↥B)=>H v.val u.val∧¬E v u)⊆ordinaryRootResources X Z→
    ordinaryHostResources (Q\D.map φ) (fun v u=>H v u∧¬ordinaryMappedSpokes E φ ψ v u)⊆
      ordinaryRootResources (X.image φ) (Z.image ψ):=by
  intro φ ψ hroot e he
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ v w=>
      have hvw:(Q\D.map φ).Adj v w:=(ordinaryHostResources_rim _ _ _).mp he
      have hp:=hparent ((ordinaryHostResources_rim Q H s(v,w)).mpr (by
        change Q.Adj v w
        exact hvw.1))
      obtain ⟨hv,hw⟩:=(ordinaryRootResources_rim_iff Y B v w).mp hp
      let v₁:↥Y:=⟨v,hv⟩
      let w₁:↥Y:=⟨w,hw⟩
      have hl:((Q.induce (Y:Set V))\D).Adj v₁ w₁:=by
        refine ⟨hvw.1,?_⟩
        intro hd
        exact hvw.2 (SimpleGraph.map_adj_apply.mpr hd)
      have hloc:=hroot ((ordinaryHostResources_rim ((Q.induce (Y:Set V))\D)
        (fun (v:↥Y) (u:↥B)=>H v.val u.val∧¬E v u) s(v₁,w₁)).mpr (by
          change ((Q.induce (Y:Set V))\D).Adj v₁ w₁
          exact hl))
      obtain ⟨hvx,hwx⟩:=(ordinaryRootResources_rim_iff X Z v₁ w₁).mp hloc
      exact ordinaryRootResources_rim (X.image φ) (Z.image ψ) v w
        (Finset.mem_image.mpr ⟨v₁,hvx,rfl⟩) (Finset.mem_image.mpr ⟨w₁,hwx,rfl⟩)
  | inr e=>
    rcases e with ⟨v,u⟩
    have hvu:H v u∧¬ordinaryMappedSpokes E φ ψ v u:=
      (ordinaryHostResources_spoke (Q\D.map φ) (fun v u=>H v u∧¬ordinaryMappedSpokes E φ ψ v u) v u).mp he
    have hp:=hparent ((ordinaryHostResources_spoke Q H v u).mpr hvu.1)
    obtain ⟨hv,hu⟩:=(ordinaryRootResources_spoke_iff Y B v u).mp hp
    let v₁:↥Y:=⟨v,hv⟩
    let u₁:↥B:=⟨u,hu⟩
    have hl:H v₁.val u₁.val∧¬E v₁ u₁:=by
      refine ⟨hvu.1,?_⟩
      intro hE
      exact hvu.2 ⟨v₁,u₁,hE,rfl,rfl⟩
    have hloc:=hroot ((ordinaryHostResources_spoke ((Q.induce (Y:Set V))\D)
      (fun (v:↥Y) (u:↥B)=>H v.val u.val∧¬E v u) v₁ u₁).mpr hl)
    obtain ⟨hvx,huz⟩:=(ordinaryRootResources_spoke_iff X Z v₁ u₁).mp hloc
    exact ordinaryRootResources_spoke (X.image φ) (Z.image ψ) v u
      (Finset.mem_image.mpr ⟨v₁,hvx,rfl⟩) (Finset.mem_image.mpr ⟨u₁,huz,rfl⟩)
end Oberwolfach
