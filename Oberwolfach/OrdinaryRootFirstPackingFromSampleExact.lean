module

public import Oberwolfach.OrdinaryRootFirstPackingContext
public import Oberwolfach.OrdinaryRootCoverNonrootData
public import Oberwolfach.OrdinaryInducedReserveSample
public import Oberwolfach.OrdinaryUnreservedPackingTransport

@[expose] public section
/-! A packing produced on the restricted post-cover host and the pulled-back
ambient reserve coins is a root-first packing on that very same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_packing_from_sample_exact
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z) (D:OrdinaryRootCoverNonrootData Q F H X T Z W r η ell)
    (σ:Sym2 (V⊕U)→Bool):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    let Q':=Q\D.rim;let H':=fun v u=>H v u∧¬D.spokes v u;
    let Qf:=Q'.induce (A:Set V);let Ff:=F.induce (A:Set V);
    let Hf:=fun (v:A) (u:B)=>H' v.val u.val;
    let σf:=fun e:Sym2 (A⊕B)=>σ (Sym2.map (φ.sumMap ψ) e);
    let Rf:=retainedGraph (ordinaryBoundaryGraph Qf Hf Xf Zf) σf;
    OrdinaryUnreservedPackingData Qf Ff Hf Xf Zf Rf r t→
      ∃K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t,
        K.cover=D.toOrdinaryRootCoverData ∧
        K.reserve=retainedGraph (ordinaryBoundaryGraph (Q\D.rim)
          (fun v u=>H v u∧¬D.spokes v u) X Z) σ:=by
  intro A B φ ψ Xf Zf Q' H' Qf Ff Hf σf Rf K
  let R:=retainedGraph (ordinaryBoundaryGraph Q' H' X Z) σ
  have he: Rf=R.comap (φ.sumMap ψ):=by
    have hh:=ordinary_induced_reserve_same_sample Q' H' X T Z W σ
    exact hh.symm
  obtain ⟨K'⟩:=ordinary_unreserved_packing_transport Qf Qf Ff Hf Hf Xf Zf Rf (R.comap (φ.sumMap ψ)) r t rfl rfl he K
  exact ⟨⟨hTX,hWZ,D.toOrdinaryRootCoverData,R,K'⟩,rfl,rfl⟩
end Oberwolfach
