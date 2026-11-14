module

public import Oberwolfach.OrdinaryRootFirstPackingFromPreCover
public import Oberwolfach.TwoStageEvents

@[expose] public section
/-! Convert a same-outcome restricted packing event into the actual ambient
root-first packing event, retaining every earlier event on that outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_precover_packing_event_to_root_first
    {V U Ω:Type} [Fintype V] [Fintype U] [Fintype Ω] [DecidableEq V] [DecidableEq U]
    (μ:FiniteLaw Ω) (E:Ω→Prop) (loss:ℝ)
    (Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop)
    (X T:Ω→Finset V) (Z W:Ω→Finset U) (r:ℕ) (η ell:ℝ) (t:Ω→ℝ)
    (D:∀s,OrdinaryRootCoverNonrootData (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r η ell)
    (σ:Ω→Sym2 (V⊕U)→Bool)
    (hTX:∀s,E s→T s⊆X s) (hWZ:∀s,E s→W s⊆Z s):
    let A:=fun s=>↥(Finset.univ\T s);let B:=fun s=>↥(Finset.univ\W s);
    let φ:=fun s=>(⟨Subtype.val,Subtype.val_injective⟩:A s↪V);
    let ψ:=fun s=>(⟨Subtype.val,Subtype.val_injective⟩:B s↪U);
    let Xf:=fun s=>(Finset.univ.filter (fun v:A s=>v.val∈X s));
    let Zf:=fun s=>(Finset.univ.filter (fun u:B s=>u.val∈Z s));
    let Df:=fun s=>(ordinaryPhysicalGraph (D s).rim (D s).spokes).comap ((φ s).sumMap (ψ s));
    let Q₀:=fun s=>((Q s).induce (↑(Finset.univ\T s):Set V))\(Df s).comap Sum.inl;
    let H₀:=fun s (v:A s) (u:B s)=>H s v.val u.val∧¬(Df s).Adj (Sum.inl v) (Sum.inr u);
    let σf:=fun s (e:Sym2 (A s⊕B s))=>σ s (Sym2.map ((φ s).sumMap (ψ s)) e);
    let R₀:=fun s=>retainedGraph (ordinaryBoundaryGraph (Q₀ s) (H₀ s) (Xf s) (Zf s)) (σf s);
    let Pack:=fun s=>OrdinaryUnreservedPackingData (Q₀ s) ((F s).induce (↑(Finset.univ\T s):Set V))
      (H₀ s) (Xf s) (Zf s) (R₀ s) r (t s);
    1-loss≤μ.probability (fun s=>E s ∧ Nonempty (Pack s))→
    1-loss≤μ.probability (fun s=>E s ∧ Nonempty
      (OrdinaryRootFirstPackingContext (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r η ell (t s))):=by
  intro A B φ ψ Xf Zf Df Q₀ H₀ σf R₀ Pack hp
  apply hp.trans
  apply finiteLaw_probability_mono
  intro s hs
  obtain ⟨K⟩:=hs.2
  refine ⟨hs.1,?_⟩
  exact ordinary_root_first_packing_from_precover (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r η ell (t s)
    (hTX s hs.1) (hWZ s hs.1) (D s) (σ s) K
end Oberwolfach
