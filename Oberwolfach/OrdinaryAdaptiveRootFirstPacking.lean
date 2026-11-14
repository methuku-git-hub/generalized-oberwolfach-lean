module

public import Oberwolfach.OrdinaryAdaptivePreCoverPacking
public import Oberwolfach.OrdinaryRootFirstPackingEventExact

@[expose] public section
/-! Turn the adaptive restricted packing event into an ambient root-first
packing event while retaining the selected cover and the same reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_root_first_packing_on_event (r:ℕ) (hr:3≤r) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δ:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧ ∀γ:ℝ,0<γ→∃η:ℝ,0<η ∧ ∃n₀:ℕ,
    ∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [LinearOrder V] [DecidableEq U],
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ),1-e≤μ.probability E→
    ∀(P Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop)
      (X T:Ω→Finset V) (Z W:Ω→Finset U) (ηcover ell:ℝ)
      (D:∀s,OrdinaryRootCoverNonrootData (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r ηcover ell)
      (σ:Ω→Sym2 (V⊕U)→Bool)
      (βparent h εparent ξ ζ p ε f binner c:ℝ),
    hpack≤h-ξ-ζ→(∀s,E s→T s⊆X s)→(∀s,E s→W s⊆Z s)→
    let A:=fun s=>↥(Finset.univ\T s);let C:=fun s=>↥(Finset.univ\W s);
    let φ:=fun s=>(⟨Subtype.val,Subtype.val_injective⟩:A s↪V);
    let ψ:=fun s=>(⟨Subtype.val,Subtype.val_injective⟩:C s↪U);
    let Xf:=fun s=>(Finset.univ.filter (fun v:A s=>v.val∈X s));
    let Zf:=fun s=>(Finset.univ.filter (fun u:C s=>u.val∈Z s));
    let Df:=fun s=>(ordinaryPhysicalGraph (D s).rim (D s).spokes).comap ((φ s).sumMap (ψ s));
    let σf:=fun s (e:Sym2 (A s⊕C s))=>σ s (Sym2.map ((φ s).sumMap (ψ s)) e);
    (∀s,E s→n₀≤Fintype.card (A s))→
    (∀s,E s→Nonempty (OrdinaryPreCoverPackingInputs r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c ell
      ((P s).induce (↑(Finset.univ\T s):Set V)) ((Q s).induce (↑(Finset.univ\T s):Set V))
      ((F s).induce (↑(Finset.univ\T s):Set V)) (fun (v:A s) (u:C s)=>H s v.val u.val)
      (Xf s) (Zf s) (Df s) (σf s)))→
    1-e≤μ.probability (fun s=>E s ∧
      ∃K:OrdinaryRootFirstPackingContext (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r ηcover ell
        (γ*Fintype.card (A s⊕C s)),
      K.cover=(D s).toOrdinaryRootCoverData ∧ K.reserve=retainedGraph
        (ordinaryBoundaryGraph (Q s\(D s).rim) (fun v u=>H s v u∧¬(D s).spokes v u) (X s) (Z s)) (σ s)):=by
  obtain ⟨N,hN⟩:=ordinary_adaptive_precover_packing_on_event r hr α hα
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,hε,hbase⟩:=hN k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,hε,?_⟩
  intro γ hγ
  obtain ⟨η,hη,n₀,hn₀⟩:=hbase γ hγ
  refine ⟨η,hη,n₀,?_⟩
  intro V U Ω _ _ _ _ _ μ E e hE P Q F H X T Z W ηcover ell D σ
    βparent h εparent ξ ζ p ε f binner c hcut hTX hWZ A C φ ψ Xf Zf Df σf hsize hdata
  have hp:=hn₀ V U Ω μ E e hE T W
    (fun s=>(P s).induce (↑(Finset.univ\T s):Set V))
    (fun s=>(Q s).induce (↑(Finset.univ\T s):Set V))
    (fun s=>(F s).induce (↑(Finset.univ\T s):Set V))
    (fun s (v:A s) (u:C s)=>H s v.val u.val) Xf Zf Df σf
    βparent h εparent ξ ζ p ε f binner c ell hcut hsize hdata
  exact ordinary_precover_packing_event_to_root_first_exact μ E e Q F H X T Z W r ηcover ell
    (fun s=>γ*Fintype.card (A s⊕C s)) D σ hTX hWZ hp
end Oberwolfach
