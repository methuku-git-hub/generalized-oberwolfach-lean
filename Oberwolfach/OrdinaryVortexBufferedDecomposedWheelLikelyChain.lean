module

public import Oberwolfach.OrdinaryDecomposedProtectedTraceLevelChain
public import Oberwolfach.OrdinaryWheelLikelyCoverCertificate
public import Oberwolfach.OrdinaryVortexInitialBufferedLocalCoverdown
public import Oberwolfach.OrdinaryVortexTraceBufferedLocalCoverdown
public import Oberwolfach.OrdinaryProtectedTraceLevelChain

@[expose] public section
/-! Local same-sample triangle probability certificates, one for each
    actual trace remainder, feed the protected level chain and absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_buffered_decomposed_wheel_likely_chain
    (P:SimpleGraph V) (D mv:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mv)
    (G₀ Pbase F:SimpleGraph V) (H₀ Hbase:V→U→Prop) (r m buffer:ℕ)
    (Wterm:Finset V) (Bterm:Finset U) (hsize:Wterm.card+Bterm.card≤m)
    (hbal:∀v,G₀.degree v=2*(Finset.univ.filter (H₀ v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H₀ v u)).card)
    (hGP:G₀≤Pbase) (hHbase:∀v u,H₀ v u→Hbase v u)
    (A:Finset (Sym2 V⊕(V×U))) (hA:A⊆ordinaryHostResources G₀ H₀)
    (hdecA:HasResourceDecomposition (ordinaryWheelResources (P:=Pbase) (F:=F) (Hbase:=Hbase) (r:=r)) A)
    (hres:∀(G':SimpleGraph V) (H':V→U→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources Wterm Bterm→
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m→
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card)→
      G'≤Pbase→(∀v u,H' v u→Hbase v u)→
      IsResourceAbsorber (ordinaryWheelResources (P:=Pbase) (F:=F) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A)
    (L:ℕ) (hL:0<L) (cost deepCost:ℕ→ℝ)
    (hc:∀i,0≤cost i) (hd:∀i,0≤deepCost i)
    (hW:Q.extendedVertices L=Wterm) (hB:Q.extendedIndices L=Bterm):
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+buffer)
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+buffer)
    let Gstart:=G₀\ordinaryResourceRim G₀ A
    let Hstart:=fun v u=>H₀ v u∧¬(Sum.inr (v,u)∈A);
    (∀i,i<L→∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryDecomposedProtectedTrace Gstart Hstart X T Z W cost deepCost r i S→
      ordinaryHostResources G Hs=S→G≤G₀→(∀v u,Hs v u→H₀ v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
      OrdinaryWheelLikelyCoverCertificate (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
        (markedVortexInnerVertices Q i) (ordinaryVortexBufferedVertices Q i buffer)
        (markedVortexInnerHubs Q i) (ordinaryVortexBufferedHubs Q i buffer) r (cost i) (deepCost i))→
    HasOrdinaryWheelDecomposition G₀ H₀ r :=by
  intro X T Z W Gstart Hstart hcert
  apply ordinary_decomposed_protected_trace_coverdown_level_chain G₀ Pbase F H₀ Hbase r m Wterm Bterm hsize hbal hdiv hGP hHbase
    A hA hdecA hres L hL X T Z W cost deepCost
      (by simpa [X, Nat.sub_add_cancel (by omega : 1≤L)] using hW)
      (by simpa [Z, Nat.sub_add_cancel (by omega : 1≤L)] using hB)
  intro i hi S G Hs htrace hstate hG hHs hbal' hdiv'
  have htrace':=ordinary_decomposed_protected_trace_forget Gstart Hstart X T Z W cost deepCost r i S htrace
  have hloc:=ordinary_wheel_likely_certificate_coverdown (G.comap (markedVortexVertexEmbedding Q i))
    (F.comap (markedVortexVertexEmbedding Q i))
    (fun v u=>Hs (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))
    (markedVortexInnerVertices Q i) (ordinaryVortexBufferedVertices Q i buffer)
    (markedVortexInnerHubs Q i) (ordinaryVortexBufferedHubs Q i buffer) r (cost i) (deepCost i)
    (hcert i hi S G Hs htrace hstate hG hHs hbal' hdiv')
  cases i with
  | zero=>
    simpa only [X,T,Z,W,Nat.zero_add] using
      ordinary_vortex_initial_buffered_local_coverdown P D mv β ε Q G F Hs r buffer (cost 0) (deepCost 0)
        (hc 0) (hd 0) hbal' hdiv' hloc
  | succ i=>
    exact ordinary_vortex_trace_buffered_local_coverdown P D mv β ε Q Gstart F Hstart cost deepCost i r buffer S G Hs
      (hc (i+1)) (hd (i+1)) htrace' hstate hbal' hdiv' hloc
end Oberwolfach
