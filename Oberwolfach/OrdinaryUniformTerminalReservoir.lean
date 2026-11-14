module

public import Oberwolfach.OrdinaryFiniteTerminalReservoir
public import Oberwolfach.OrdinaryTriangleAbsorberHighProbability
public import Oberwolfach.OrdinaryActiveRootImages

@[expose] public section
/-! A uniform one-sample absorber event supplies one fixed reservoir for a
finite collection of terminal remainders. The common root pair may contain
more rows or hubs than those actually used by any one remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_uniform_terminal_reservoir
    (r m l f a b f₀:ℕ) (γ ε:ℝ)
    (Q F:SimpleGraph V) (H:V→U→Prop) (W:Finset V) (B:Finset U)
    (hW:W.card≤f) (hB:(B.card:ℝ)≤γ)
    (hWbudget:f+l*a≤f₀) (hBbudget:γ+l*b≤ε*Fintype.card V+f₀)
    (G:Fin l→SimpleGraph V) (Hs:Fin l→V→U→Prop)
    (hsize:∀i,(ordinaryPhysicalGraph (G i) (Hs i)).support.toFinset.card≤m)
    (hbalance:∀i v,(G i).degree v=2*(Finset.univ.filter (Hs i v)).card)
    (hdiv:∀i u,r∣(Finset.univ.filter (fun v=>Hs i v u)).card)
    (hG:∀i,G i≤Q) (hH:∀i v u,Hs i v u→H v u)
    (hrows:∀i,(G i).support.toFinset⊆W)
    (hactive:∀i u,(∃v,Hs i v u)→u∈B)
    (hlocal:∀(G':SimpleGraph V) (H':V→U→Prop) (W':Finset V) (B':Finset U),
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤Q → (∀v u,H' v u→H v u) →
      (∀u,(∃v,H' v u)→u∈B') → W'.card≤f₀ →
      (B'.card:ℝ)≤ε*Fintype.card V+f₀ →
      ∃C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G' H') C ∧
        C⊆ordinaryHostResources Q H ∧ (ordinaryResourceRows C).card≤a ∧
        (ordinaryResourceHubs C).card≤b ∧ Disjoint C (ordinaryRootResources W' B')):
    ∃C:Finset (Sym2 V⊕(V×U)),C⊆ordinaryHostResources Q H ∧
      Disjoint C (ordinaryRootResources W B) ∧
      (ordinaryResourceRows C).card≤l*a ∧ (ordinaryResourceHubs C).card≤l*b ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) C ∧
      ∀i,IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
        (ordinaryHostResources (G i) (Hs i)) C:=by
  apply ordinary_finite_terminal_reservoir l f a b γ W B hW hB
    (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources Q H)
    (fun i=>ordinaryHostResources (G i) (Hs i))
  · intro i
    apply ordinaryRootResources_contains
    · rw [ordinary_resources_active_rows (G i) (Hs i) (hbalance i)]
      exact hrows i
    · rw [ordinary_resources_active_hubs (G i) (Hs i)]
      intro u hu
      exact hactive i u (Finset.mem_filter.mp hu).2
  · intro W' B' hWW hBB hw hb i
    apply hlocal (G i) (Hs i) W' B' (hsize i) (hbalance i) (hdiv i) (hG i) (hH i)
    · intro u hu
      exact hBB (hactive i u hu)
    · exact hw.trans hWbudget
    · exact hb.trans hBbudget
end Oberwolfach
