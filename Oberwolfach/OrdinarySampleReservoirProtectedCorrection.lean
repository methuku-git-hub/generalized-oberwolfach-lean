module

public import Oberwolfach.OrdinaryReservoirAndProtectedCorrection
public import Oberwolfach.OrdinaryGlobalCorrectionSampleInputs

@[expose] public section
/-! The terminal reservoir and protected correction use the same sampled
host, with the correction cuts and balance derived from sampled tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sample_reservoir_and_protected_correction
    (r m t f a b:ℕ) (hr:3≤r) (ε ω h δ ξ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4) (hξ:0<ξ) (hξh:ξ≤h/100)
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (η:ℝ) (hη:0≤η)
    (hηsmall:η≤(ordinarySparseCorrectionParameters r hr ω h δ ξ hω hh hδ hδsmall hξ hξh).1)
    (hn:(ordinarySparseCorrectionParameters r hr ω h δ ξ hω hh hδ hδsmall hξ hξh).2≤Fintype.card V)
    (hnpos:0<Fintype.card V) (hupos:0<Fintype.card U)
    (hωn:ω*Fintype.card V≤Fintype.card U) (hUn:Fintype.card U≤Fintype.card V)
    (P F:SimpleGraph V) (D:ℕ) (hreg:P.IsRegularOfDegree D)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
    (pR pH tR tH L:ℝ) (s:U→Color→ℝ)
    (htR:0≤tR) (htH:0≤tH) (hL:0≤L) (hmean:pR*D=2*pH*Fintype.card U)
    (hrows:RawOrdinaryRows P π d 2 Finset.univ pR s j tR σ)
    (hcols:RawOrdinaryDomainIndices F π d 3 Finset.univ pH j tH σ)
    (hF:∀v,(F.degree v:ℝ)≤L) (hbudget:tR+2*tH+3*L≤η*Fintype.card V)
    (hcuts:OrdinaryTriangleReferenceMatrixCuts P F π d j δ h σ coins)
    (A Z Wterm W:Finset V) (Bterm B:Finset U)
    (hA:A=Finset.univ\Z) (hZ:(Z.card:ℝ)≤ε*Fintype.card V)
    (hsize:Wterm.card+Bterm.card≤t) (hWW:Wterm⊆W) (hBB:Bterm⊆B)
    (hW:W.card≤f) (hB:(B.card:ℝ)≤ε*Fintype.card V+f)
    (ζ:ℝ) (hζ:0≤ζ) (hζh:ζ≤h)
    (hTbudget:((Z.card+2^(t*t)*a:ℕ):ℝ)≤ζ*Fintype.card V)
    (hBbudget:((B.card+2^(t*t)*b:ℕ):ℝ)≤ζ*Fintype.card U):
    let Q:=rawWheelGraph P σ\F;
    let H:=rawWheelSpokes π d σ j;
    let R:=ordinarySampledOrientedRelation Q coins;
    OrdinaryUniformProtectedReservoirEvent r m t f a b ε Q F H →
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
        (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V) :=by
  intro Q H R hRes
  have hi:=ordinary_global_correction_sample_inputs P F D hreg π d j σ coins pR pH tR tH L η δ h s
    hnpos hupos htR htH hL hmean hrows hcols hF hbudget hcuts
  have hout:=ordinary_reservoir_and_protected_correction r m t f a b hr ε ω h δ ξ hω hh hδ hδsmall hξ hξh V U η hη hηsmall
    hn hnpos hωn hUn Q F H R hRes A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB ζ hζ hζh hTbudget hBbudget
    (by intro x y;convert hi.1 x y using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hi.2.1 hi.2.2.1
    (by intro v;convert hi.2.2.2 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  convert hout using 1
  funext K
  congr! 50
end Oberwolfach
