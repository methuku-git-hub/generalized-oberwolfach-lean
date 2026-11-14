module

public import Oberwolfach.OrdinaryPreCoverPackingFixedCut
public import Oberwolfach.OrdinaryUnreservedNearBalancePackingLinear
public import Oberwolfach.OrdinaryNearBalanceCutWeaken

@[expose] public section
/-! The pre-cover structural data, root-cover deletion, reserve and actual
nonroot packing remain on the same sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_precover_packing_on_event_linear (r:ℕ) (hr:3≤r) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δ:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δ→δ<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧ ∀γ:ℝ,0<γ→γ≤1→∃η:ℝ,0<η ∧ cLinear*γ≤η ∧ ∃n₀:ℕ,
    ∀(V U Ω:Type) [Fintype V] [Fintype U] [Fintype Ω] [LinearOrder V] [DecidableEq U],
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ),1-e≤μ.probability E→
    ∀(T:Ω→Finset V) (W:Ω→Finset U),
    let A:=fun s=>↥(Finset.univ\T s);let C:=fun s=>↥(Finset.univ\W s);
    ∀(P Q F:∀s,SimpleGraph (A s)) (H:∀s,A s→C s→Prop)
      (X:∀s,Finset (A s)) (Z:∀s,Finset (C s)) (D:∀s,SimpleGraph (A s⊕C s))
      (σ:∀s,Sym2 (A s⊕C s)→Bool)
      (βparent h εparent ξ ζ p ε f binner c L:ℝ),
    hpack≤h-ξ-ζ→
    (∀s,E s→n₀≤Fintype.card (A s))→
    (∀s,E s→Nonempty (OrdinaryPreCoverPackingInputs r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c L
      (P s) (Q s) (F s) (H s) (X s) (Z s) (D s) (σ s)))→
    1-e≤μ.probability (fun s=>E s ∧
      let Q':=Q s\(D s).comap Sum.inl;
      let H':=fun v u=>H s v u∧¬(D s).Adj (Sum.inl v) (Sum.inr u);
      let R:=retainedGraph (ordinaryBoundaryGraph Q' H' (X s) (Z s)) (σ s);
      Nonempty (OrdinaryUnreservedPackingData Q' (F s) H' (X s) (Z s) R r
        (γ*Fintype.card (A s⊕C s)))):=by
  obtain ⟨N,hN⟩:=ordinary_unreserved_near_balance_packing_linear r hr α hα
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,cLinear,hε,hcLinear,hpack_rule⟩:=hN k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,cLinear,hε,hcLinear,?_⟩
  intro γ hγ hγone
  obtain ⟨η,hη,hlinear,n₀,hn₀⟩:=hpack_rule γ hγ hγone
  refine ⟨η,hη,hlinear,n₀,?_⟩
  intro V U Ω _ _ _ _ _ μ E e hE T W A C P Q F H X Z D σ
    βparent h εparent ξ ζ p ε f binner c L hcut hsize hdata
  apply hE.trans
  apply finiteLaw_probability_mono
  intro s hs
  obtain ⟨d⟩:=hdata s hs
  let Q':=Q s\(D s).comap Sum.inl
  let H':=fun v u=>H s v u∧¬(D s).Adj (Sum.inl v) (Sum.inr u)
  let R:=retainedGraph (ordinaryBoundaryGraph Q' H' (X s) (Z s)) (σ s)
  obtain ⟨dfinal⟩:=ordinary_precover_packing_data_fixed_cut r hr k α ω βparent β b B h hpack δ εparent εstar η ξ ζ p ε f binner c L
    (P s) (Q s) (F s) (H s) (X s) (Z s) (D s) (σ s) hcut d
  refine ⟨hs,?_⟩
  apply hn₀ (A s) (C s) (hsize s hs) (P s) Q' (F s) H' (X s) (Z s) R
  convert dfinal using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
