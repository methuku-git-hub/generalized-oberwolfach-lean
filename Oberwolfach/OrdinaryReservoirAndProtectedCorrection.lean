module

public import Oberwolfach.OrdinaryReservoirCorrectionProtectionPair
public import Oberwolfach.OrdinaryProtectedCorrectionModular

@[expose] public section
/-! Select the terminal reservoir first, then construct a sparse correction
protecting both the inner pair and every occupied reservoir row and hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reservoir_and_protected_correction
    (r m t f a b:ℕ) (hr:3≤r) (ε ω h δ ξ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4) (hξ:0<ξ) (hξh:ξ≤h/100)
    (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (η:ℝ) (hη:0≤η)
    (hηsmall:η≤(ordinarySparseCorrectionParameters r hr ω h δ ξ hω hh hδ hδsmall hξ hξh).1)
    (hn:(ordinarySparseCorrectionParameters r hr ω h δ ξ hω hh hδ hδsmall hξ hξh).2≤Fintype.card V)
    (hnpos:0<Fintype.card V) (hωn:ω*Fintype.card V≤Fintype.card U) (hUn:Fintype.card U≤Fintype.card V)
    (Q F:SimpleGraph V) (H:V→U→Prop) (R:V→V→Prop)
    (hRes:OrdinaryUniformProtectedReservoirEvent r m t f a b ε Q F H)
    (A Z Wterm W:Finset V) (Bterm B:Finset U)
    (hA:A=Finset.univ\Z) (hZ:(Z.card:ℝ)≤ε*Fintype.card V)
    (hsize:Wterm.card+Bterm.card≤t) (hWW:Wterm⊆W) (hBB:Bterm⊆B)
    (hW:W.card≤f) (hB:(B.card:ℝ)≤ε*Fintype.card V+f)
    (ζ:ℝ) (hζ:0≤ζ) (hζh:ζ≤h)
    (hTbudget:((Z.card+2^(t*t)*a:ℕ):ℝ)≤ζ*Fintype.card V)
    (hBbudget:((B.card+2^(t*t)*b:ℕ):ℝ)≤ζ*Fintype.card U)
    (hOrient:∀x y,relationMultiplicity R x y+relationMultiplicity R y x=if Q.Adj x y then 1 else 0)
    (hcutR:BipartiteLargeCut (relationMultiplicity R) δ (2*h))
    (hcutH:BipartiteLargeCut (relationMultiplicity H) δ (2*h))
    (hbal:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤η*Fintype.card V):
    ∃K:Finset (Sym2 V⊕(V×U)),
      K⊆ordinaryHostResources Q H ∧ Disjoint K (ordinaryRootResources Z B) ∧
      (ordinaryResourceRows K).card≤2^(t*t)*a ∧ (ordinaryResourceHubs K).card≤2^(t*t)*b ∧
      ordinaryResourceRows K⊆Wterm∪A ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) K ∧
      (∀(G:SimpleGraph V) (Hs:V→U→Prop),
        ordinaryHostResources G Hs⊆ordinaryRootResources Wterm Bterm →
        (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m →
        (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
        (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) →
        G≤Q → (∀v u,Hs v u→H v u) →
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G Hs) K) ∧
      ∃(JQ:SimpleGraph V) (JH:V→U→Prop),
        JQ≤Q ∧ (∀v∈Z,∀w∈Z,¬JQ.Adj v w) ∧
        (∀v u,JH v u→H v u ∧ ¬(v∈Z ∧ u∈B)) ∧
        K⊆ordinaryHostResources (Q\JQ) (fun v u=>H v u∧¬JH v u) ∧
        (∀v,(Q\JQ).degree v=2*(Finset.univ.filter (fun u=>H v u ∧ ¬JH v u)).card) ∧
        (∀u,r∣(Finset.univ.filter (fun v=>H v u ∧ ¬JH v u)).card) ∧
        (∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V) ∧
        (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V):=by
  obtain ⟨K,hK,havoid,hrows,hhubs,hrowsloc,hdec,habs,hsurvive⟩:=
    ordinary_uniform_reservoir_before_protected_correction r m t f a b ε Q F H hRes A Z Wterm W Bterm B
      hA hZ hsize hWW hBB hW hB
  let T:=Z∪ordinaryResourceRows K
  let B':=B∪ordinaryResourceHubs K
  have hp:=ordinary_reservoir_correction_protection_pair Q H K Z B (2^(t*t)*a) (2^(t*t)*b) hK hrows hhubs
  change Z⊆T ∧ B⊆B' ∧ T.card≤Z.card+2^(t*t)*a ∧ B'.card≤B.card+2^(t*t)*b ∧ _ at hp
  have hT:(T.card:ℝ)≤ζ*Fintype.card V:=(Nat.cast_le.mpr hp.2.2.1).trans hTbudget
  have hB':(B'.card:ℝ)≤ζ*Fintype.card U:=(Nat.cast_le.mpr hp.2.2.2.1).trans hBbudget
  obtain ⟨JQ,JH,hJQ,hJQavoid,hJH,hbalance,hdiv,hrow,hcol⟩:=
    ordinary_protected_correction_at_order_modular r hr ω h δ ξ hω hh hδ hδsmall hξ hξh V U η hη hηsmall
      hn hnpos hωn hUn Q H R T B' ζ hζ hζh hT hB' hOrient hcutR hcutH hbal
  have hprotect:=hp.2.2.2.2 JQ JH hJQavoid (fun v u hv=>(hJH v u hv).2)
  refine ⟨K,hK,havoid,hrows,hhubs,hrowsloc,hdec,habs,JQ,JH,hJQ,hprotect.2.1,?_,hprotect.1,hbalance,hdiv,hrow,hcol⟩
  intro v u hv
  exact ⟨(hJH v u hv).1,hprotect.2.2 v u hv⟩
end Oberwolfach
