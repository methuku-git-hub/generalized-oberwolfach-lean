module

public import Oberwolfach.OrdinaryRootFirstPackingFromSample
public import Oberwolfach.OrdinaryInducedCoverDeletion

@[expose] public section
/-! The packing constructed after deleting the pulled-back root cover
is the actual root-first packing on the same ambient reserve sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_packing_from_precover
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z) (D:OrdinaryRootCoverNonrootData Q F H X T Z W r η ell)
    (σ:Sym2 (V⊕U)→Bool):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset B:=Finset.univ.filter (fun u=>u.val∈Z);
    let Df:=(ordinaryPhysicalGraph D.rim D.spokes).comap (φ.sumMap ψ);
    let Qf:=Q.induce (A:Set V);let Ff:=F.induce (A:Set V);
    let Hf:=fun (v:A) (u:B)=>H v.val u.val;
    let Q₀:=Qf\Df.comap Sum.inl;
    let H₀:=fun v u=>Hf v u∧¬Df.Adj (Sum.inl v) (Sum.inr u);
    let σf:=fun e:Sym2 (A⊕B)=>σ (Sym2.map (φ.sumMap ψ) e);
    let R₀:=retainedGraph (ordinaryBoundaryGraph Q₀ H₀ Xf Zf) σf;
    OrdinaryUnreservedPackingData Q₀ Ff H₀ Xf Zf R₀ r t→
      Nonempty (OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t):=by
  intro A B φ ψ Xf Zf Df Qf Ff Hf Q₀ H₀ σf R₀ K
  let Q':=Q\D.rim
  let H':=fun v u=>H v u∧¬D.spokes v u
  let Q₁:=Q'.induce (A:Set V)
  let H₁:=fun (v:A) (u:B)=>H' v.val u.val
  let R₁:=retainedGraph (ordinaryBoundaryGraph Q₁ H₁ Xf Zf) σf
  have he:=ordinary_induced_cover_deletion_pair Q D.rim H D.spokes T W
  have hQ:Q₀=Q₁:=he.1
  have hH:H₀=H₁:=he.2
  have hR:R₀=R₁:=by
    dsimp only [R₀,R₁]
    rw [hQ,hH]
  obtain ⟨K₁⟩:=ordinary_unreserved_packing_transport Q₀ Q₁ Ff H₀ H₁ Xf Zf R₀ R₁ r t hQ hH hR K
  exact ordinary_root_first_packing_from_sample Q F H X T Z W r η ell t hTX hWZ D σ K₁
end Oberwolfach
