module

public import Oberwolfach.OrdinaryRootCoverReferenceWithReserve
public import Oberwolfach.OrdinaryAdaptiveNonrootReserveToInput

@[expose] public section
/-! On the same expanded outcome, an actual selected root cover and the
ambient reserve coins supply the post-cover packing inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_root_cover_inputs_event (q:ℕ) (ε:ℝ) (hε:0<ε):
    ∃N:ℕ,∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [LinearOrder V] [DecidableEq U],
      ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀ loss:ℝ),0≤loss→1-e₀≤μ.probability E→
      ∀(P Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop)
        (X T:Ω→Finset V) (Z W:Ω→Finset U) (r k:ℕ) (hr:3≤r) (ηcover ell b₀ c₀:ℝ)
        (D:∀s,OrdinaryRootCoverNonrootData (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r ηcover ell)
        (α ω βparent β b B h δ εparent εstar η ξ ζ p f binner c:ℝ)
        (hp:0≤p) (hp1:p≤1),
      let A:=fun s=>↥(Finset.univ\T s);let C:=fun s=>↥(Finset.univ\W s);
      let φ:=fun s=>(⟨Subtype.val,Subtype.val_injective⟩:A s↪V);
      let ψ:=fun s=>(⟨Subtype.val,Subtype.val_injective⟩:C s↪U);
      let Xf:=fun s=>(Finset.univ.filter (fun v:A s=>v.val∈X s));
      let Zf:=fun s=>(Finset.univ.filter (fun u:C s=>u.val∈Z s));
      let Qf:=fun s=>((Q s\(D s).rim).induce (↑(Finset.univ\T s):Set V));
      let Hf:=fun s (v:A s) (u:C s)=>H s v.val u.val∧¬(D s).spokes v.val u.val;
      let Df:=fun s=>(ordinaryPhysicalGraph (D s).rim (D s).spokes).comap ((φ s).sumMap (ψ s));
      (∀s,E s→N≤Fintype.card (A s⊕C s))→
      (∀s,E s→1/(Fintype.card (A s⊕C s):ℝ)^q≤loss)→
      (∀s,E s→Nonempty (OrdinaryRootCoverReferenceData (P s) (Q s) (F s) (H s) (X s) (T s) (Z s) (W s)
        r k hr ηcover ell b₀ c₀ (D s) α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c))→
      let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp hp1);
      1-(e₀+loss)≤(μ.sigma (fun _=>ν)).probability (fun z=>E z.1 ∧
        Nonempty (OrdinaryPreCoverPackingInputs r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c ell
          ((P z.1).induce (↑(Finset.univ\T z.1):Set V)) ((Q z.1).induce (↑(Finset.univ\T z.1):Set V))
          ((F z.1).induce (↑(Finset.univ\T z.1):Set V)) (fun (v:A z.1) (u:C z.1)=>H z.1 v.val u.val)
          (Xf z.1) (Zf z.1) (Df z.1) (fun e=>z.2 (Sym2.map ((φ z.1).sumMap (ψ z.1)) e)))):=by
  obtain ⟨N,hN⟩:=ordinary_adaptive_nonroot_reserve_to_input q ε hε
  refine ⟨N,?_⟩
  intro V U Ω _ _ _ _ _ μ E e₀ loss hloss hE P Q F H X T Z W r k hr ηcover ell b₀ c₀ D
    α ω βparent β b B h δ εparent εstar η ξ ζ p f binner c hp hp1
    A C φ ψ Xf Zf Qf Hf Df hsize hbound hdata ν
  let Input:=fun s (σ:Sym2 (A s⊕C s)→Bool)=>
    Nonempty (OrdinaryPreCoverPackingInputs r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c ell
      ((P s).induce (↑(Finset.univ\T s):Set V)) ((Q s).induce (↑(Finset.univ\T s):Set V))
      ((F s).induce (↑(Finset.univ\T s):Set V)) (fun (v:A s) (u:C s)=>H s v.val u.val)
      (Xf s) (Zf s) (Df s) σ)
  have hh:=hN V U Ω μ E e₀ loss hloss hE T W Qf Hf Xf Zf Input hsize hbound p hp hp1 (by
    intro s hs σ hgood
    obtain ⟨d⟩:=hdata s hs
    exact ordinary_root_cover_reference_with_reserve (P s) (Q s) (F s) (H s) (X s) (T s) (Z s) (W s)
      r k hr ηcover ell b₀ c₀ (D s) α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c d σ hgood)
  exact hh
end Oberwolfach
