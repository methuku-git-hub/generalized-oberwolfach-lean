module

public import Oberwolfach.OrdinaryVortexUniformWheelChainTwoHosts
public import Oberwolfach.OrdinaryWheelHostLift

@[expose] public section
/-! A reservoir whose wheels live in a reference host can absorb the terminal
remainder while the cover-down runs in the actual host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_reference_absorber_chain
    (P:SimpleGraph V) (D mv:ℕ) (β ε:ℝ) (Vor:Vortex U P D β ε mv)
    (G₀ Ref F:SimpleGraph V) (H₀ Href:V→U→Prop) (r m:ℕ)
    (Wterm:Finset V) (Bterm:Finset U) (hsize:Wterm.card+Bterm.card≤m)
    (hbal:∀v,G₀.degree v=2*(Finset.univ.filter (H₀ v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H₀ v u)).card)
    (hP:∀v∈Wterm,∀w∈Wterm,G₀.Adj v w→Ref.Adj v w)
    (hH:∀v∈Wterm,∀u∈Bterm,H₀ v u→Href v u)
    (A:Finset (Sym2 V⊕(V×U))) (hA:A⊆ordinaryHostResources G₀ H₀)
    (hdecA:HasResourceDecomposition (ordinaryWheelResources (P:=Ref) (F:=F) (Hbase:=Href) (r:=r)) A)
    (hres:∀(G':SimpleGraph V) (H':V→U→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources Wterm Bterm→
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m→
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card)→
      G'≤Ref→(∀v u,H' v u→Href v u)→
      IsResourceAbsorber (ordinaryWheelResources (P:=Ref) (F:=F) (Hbase:=Href) (r:=r))
        (ordinaryHostResources G' H') A)
    (L:ℕ) (hL:0<L) (cost deepCost:ℕ→ℝ)
    (hc:∀i,0≤cost i) (hd:∀i,0≤deepCost i)
    (hW:Vor.extendedVertices L=Wterm) (hB:Vor.extendedIndices L=Bterm):
    let X:=fun k=>Vor.extendedVertices (k+1);let T:=fun k=>Vor.extendedVertices (k+2)
    let Z:=fun k=>Vor.extendedIndices (k+1);let W:=fun k=>Vor.extendedIndices (k+2)
    let Gstart:=G₀\ordinaryResourceRim G₀ A
    let Hstart:=fun v u=>H₀ v u∧¬(Sum.inr (v,u)∈A);
    (∀i,i<L→∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Z W cost deepCost r i L S
        (fun t=>Vor.extendedVertices (t+2)) (fun t=>Vor.extendedVertices (t+1)) (fun t=>Vor.extendedIndices (t+2))
        (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
      ordinaryHostResources G Hs=S→G≤G₀→(∀v u,Hs v u→H₀ v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      let f:=markedVortexVertexEmbedding Vor i;let g:=markedVortexHubEmbedding Vor i;
      OrdinaryWheelLikelySeparateCostsCertificate (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
        (markedVortexInnerVertices Vor i) (ordinaryVortexBufferedVertices Vor i 2)
        (markedVortexInnerHubs Vor i) (ordinaryVortexBufferedHubs Vor i 2) r (cost i) (deepCost i))→
    HasOrdinaryWheelDecomposition G₀ H₀ r :=by
  intro X T Z W Gstart Hstart hcert
  let Base:SimpleGraph V:=G₀⊔Ref
  let Hbase:V→U→Prop:=fun v u=>H₀ v u∨Href v u
  have hRef:Ref≤Base:=le_sup_right
  have hHref:∀v u,Href v u→Hbase v u:=fun _ _ h=>Or.inr h
  have hdec:HasResourceDecomposition (ordinaryWheelResources (P:=Base) (F:=F) (Hbase:=Hbase) (r:=r)) A:=
    ordinary_wheel_host_decomposition_lift hRef hHref A hdecA
  exact ordinary_vortex_two_step_uniform_wheel_chain_two_hosts P D mv β ε Vor G₀ Base Ref F H₀ Hbase Href r m
    Wterm Bterm hsize hbal hdiv le_sup_left (fun _ _ h=>Or.inl h) hRef hHref hP hH A hA hdec hres
    L hL cost deepCost hc hd hW hB hcert
end Oberwolfach
