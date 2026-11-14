module

public import Oberwolfach.MarkedFreshHubCommonEvent
public import Oberwolfach.MarkedEmbeddedHubFactors
public import Oberwolfach.MarkedActiveDeletionDegrees

@[expose] public section

/-! The fresh factor event on an inner row domain is read under the
original ambient physical coin law. Its tolerance is chosen before the
inner/ambient size ratio, the embedding, and the boundary sampling rate.
Every later class and forbidden graph is covered by this same event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedInnerCoinEmbedding {W V U:Type} (f:W↪V):Sym2 (W⊕U)↪Sym2 (V⊕U):=
  (show W⊕U↪V⊕U from ⟨Sum.map f id,Sum.map_injective.mpr ⟨f.injective,Function.injective_id⟩⟩).sym2Map

theorem marked_embedded_fresh_hub_common_event (m:ℕ) (hm:3<m+1) (β κ bLo B:ℝ)
    (hβ:0<β) (hκ:0<κ) (hbLo:0<bLo) (hB:0≤B):
    ∃ η ζ:ℝ,0<η∧0<ζ∧∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
    ∀ (W V U E K J:Type) [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
      [Fintype U] [DecidableEq U] [Fintype J],
    N≤Fintype.card W→Fintype.card J≤(Fintype.card W)^2→
    ∀ (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V),(∀ x,f (ρ x)=π (f x))→
    ∀ (tail head:E→W) (ktail khead:K→W) (b:ℕ) (H₀ HK:W→U→Prop) (u:J→U),
    (∀ j v,¬(H₀ v (u j)∧HK v (u j)))→
    Function.Injective (markedPhysicalEdge tail head ktail khead ρ)→
    (∀ j v z,H₀ v (u j)→HK z (u j)→v≠ρ z)→
    (∀ j,κ*Fintype.card W≤((Finset.univ.filter (fun v=>H₀ v (u j)∨HK v (u j))).card:ℝ))→
    (∀ j,β*(Fintype.card W:ℝ)^(m+1)≤Fintype.card (HubMarkedCycle tail head ktail khead m ρ b H₀ HK (u j)))→
    (∀ j i,∀ v v':W,v≠v'→(if i then HK v (u j) else H₀ v (u j))→(if i then HK v' (u j) else H₀ v' (u j))→
      β*(Fintype.card W:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m ρ b H₀ HK i v v' (u j) (u j)))→
    ∀ wt:∀ j,HubMarkedCycle tail head ktail khead m ρ b H₀ HK (u j)→ℝ,
    (∀ j C,bLo/(Fintype.card W:ℝ)^m≤wt j C∧wt j C≤B/(Fintype.card W:ℝ)^m)→
    (∀ j v,H₀ v (u j)∨HK v (u j)→|1-hypergraphWeightedDegree (hubMarkedCycleVertices (u j)) (wt j) v|≤η)→
    1-1/(Fintype.card W:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>∀ j (Y:Finset W),(∀ v∈Y,H₀ v (u j)∨HK v (u j))→
          (Y.filter (fun v=>H₀ v (u j))).card=m*(Y.filter (fun v=>HK v (u j))).card→
          ((changed Y ((Finset.univ.filter (fun v=>H₀ v (u j)∨HK v (u j))).filter
            (fun v=>σ s(Sum.inl (f v),Sum.inr (u j))=true))).card:ℝ)≤ζ*(p*Fintype.card W)→
          ∀ F:SimpleGraph V,(∀ v,(F.degree v:ℝ)≤ζ*(p*Fintype.card W))→
          ∃ P:MarkedHubFactorOn (f∘tail) (f∘head) (f∘ktail) (f∘khead) m π b
            (spokeRelationImage f H₀) (spokeRelationImage f HK) (u j) (Y.image f),Disjoint P.rim F):=by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=marked_fresh_hub_common_event m hm β κ bLo B hβ hκ hbLo hB
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro W V U E K J _ _ _ _ _ _ _ hn hJ f ρ π hf tail head ktail khead b H₀ HK u
    hdis hphys hsep hsize hcycles hpaths wt hw herr
  have hevent:=hN W U E K J hn hJ tail head ktail khead ρ b H₀ HK u
    hdis hphys hsep hsize hcycles hpaths wt hw herr
  rw [←finiteLaw_pi_injective_projection_event
    (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)
    (markedInnerCoinEmbedding (U:=U) f) (markedInnerCoinEmbedding (U:=U) f).injective] at hevent
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ j Y hY hratio hchange F hF
  have hdegree:∀ x,((F.comap f).degree x:ℝ)≤ζ*(p*Fintype.card W):=by
    intro x
    have hh:=graph_comap_injective_degree_le F f x
    exact (show ((F.comap f).degree x:ℝ)≤(F.degree (f x):ℝ) by exact_mod_cast hh).trans (hF (f x))
  obtain ⟨D,hD,havoid,_hdeg,_hedge⟩:=hσ j Y hY hratio hchange (F.comap f) hdegree
  let P:MarkedHubFactorOn tail head ktail khead m ρ b H₀ HK (u j) Y:=⟨D,hD.1,hD.2⟩
  exact ⟨hubFactorEmbedding f ρ π hf tail head ktail khead m b H₀ HK (u j) Y P,
    hubFactorEmbedding_avoids f ρ π hf tail head ktail khead m b H₀ HK (u j) Y P F havoid⟩

end Oberwolfach
