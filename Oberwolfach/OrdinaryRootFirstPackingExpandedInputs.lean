module

public import Oberwolfach.OrdinaryAdaptiveRootFirstPacking

@[expose] public section
/-! Apply adaptive root-first packing to pre-cover inputs already known on
an expanded common-sample event, preserving the earlier event and coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_packing_from_expanded_inputs (r:ℕ) (hr:3≤r) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δ:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧ ∀γ:ℝ,0<γ→∃η:ℝ,0<η ∧ ∃n₀:ℕ,
    ∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [LinearOrder V] [DecidableEq U],
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ)
      (P Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop)
      (X T:Ω→Finset V) (Z W:Ω→Finset U) (ηcover ell:ℝ)
      (D:∀s,OrdinaryRootCoverNonrootData (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r ηcover ell)
      (βparent h εparent ξ ζ p ε f binner c:ℝ) (hp:0≤p) (hp1:p≤1),
    hpack≤h-ξ-ζ→(∀s,E s→T s⊆X s)→(∀s,E s→W s⊆Z s)→
    let A:=fun s=>↥(Finset.univ\T s);let C:=fun s=>↥(Finset.univ\W s);
    let φ:=fun s=>(⟨Subtype.val,Subtype.val_injective⟩:A s↪V);
    let ψ:=fun s=>(⟨Subtype.val,Subtype.val_injective⟩:C s↪U);
    let Xf:=fun s=>(Finset.univ.filter (fun v:A s=>v.val∈X s));
    let Zf:=fun s=>(Finset.univ.filter (fun u:C s=>u.val∈Z s));
    let Df:=fun s=>(ordinaryPhysicalGraph (D s).rim (D s).spokes).comap ((φ s).sumMap (ψ s));
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp hp1);
    (∀s,E s→n₀≤Fintype.card (A s))→
    1-e≤(μ.sigma (fun _=>law)).probability (fun z=>E z.1 ∧
      Nonempty (OrdinaryPreCoverPackingInputs r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c ell
        ((P z.1).induce (↑(Finset.univ\T z.1):Set V)) ((Q z.1).induce (↑(Finset.univ\T z.1):Set V))
        ((F z.1).induce (↑(Finset.univ\T z.1):Set V)) (fun (v:A z.1) (u:C z.1)=>H z.1 v.val u.val)
        (Xf z.1) (Zf z.1) (Df z.1) (fun e=>z.2 (Sym2.map ((φ z.1).sumMap (ψ z.1)) e))))→
    1-e≤(μ.sigma (fun _=>law)).probability (fun z=>E z.1 ∧
      ∃K:OrdinaryRootFirstPackingContext (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1) r ηcover ell
        (γ*Fintype.card (A z.1⊕C z.1)),
      K.cover=(D z.1).toOrdinaryRootCoverData ∧ K.reserve=retainedGraph
        (ordinaryBoundaryGraph (Q z.1\(D z.1).rim) (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) (Z z.1)) z.2):=by
  obtain ⟨N,hN⟩:=ordinary_adaptive_root_first_packing_on_event r hr α hα
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,hε,hbase⟩:=hN k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,hε,?_⟩
  intro γ hγ
  obtain ⟨η,hη,n₀,hn₀⟩:=hbase γ hγ
  refine ⟨η,hη,n₀,?_⟩
  intro V U Ω _ _ _ _ _ μ E e P Q F H X T Z W ηcover ell D βparent h εparent ξ ζ p ε f binner c hp hp1
    hcut hTX hWZ A C φ ψ Xf Zf Df law hsize hprob
  let Good:=fun z:(Σ _ : Ω,Sym2 (V⊕U)→Bool)=>E z.1 ∧
      Nonempty (OrdinaryPreCoverPackingInputs r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c ell
        ((P z.1).induce (↑(Finset.univ\T z.1):Set V)) ((Q z.1).induce (↑(Finset.univ\T z.1):Set V))
        ((F z.1).induce (↑(Finset.univ\T z.1):Set V)) (fun (v:A z.1) (u:C z.1)=>H z.1 v.val u.val)
        (Xf z.1) (Zf z.1) (Df z.1) (fun e=>z.2 (Sym2.map ((φ z.1).sumMap (ψ z.1)) e)))
  have hh:=hn₀ V U (Σ _ : Ω,Sym2 (V⊕U)→Bool) (μ.sigma (fun _=>law)) Good e hprob
    (fun z=>P z.1) (fun z=>Q z.1) (fun z=>F z.1) (fun z=>H z.1)
    (fun z=>X z.1) (fun z=>T z.1) (fun z=>Z z.1) (fun z=>W z.1) ηcover ell (fun z=>D z.1) (fun z=>z.2)
    βparent h εparent ξ ζ p ε f binner c hcut (by intro z hz;exact hTX z.1 hz.1)
    (by intro z hz;exact hWZ z.1 hz.1) (by intro z hz;exact hsize z.1 hz.1) (by intro z hz;exact hz.2)
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1.1,hz.2⟩
end Oberwolfach
