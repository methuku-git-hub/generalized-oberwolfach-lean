module

public import Oberwolfach.OrdinaryUniformTerminalReservoir

@[expose] public section
/-! A single sampled wheel-absorber event yields one reservoir that
absorbs every member of a fixed finite family of terminal remainders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_sample_terminal_reservoir
    (r m l f a b f₀:ℕ) (γ ε:ℝ) (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (j:Color) (A Z W:Finset V) (B:Finset U)
    (hA:A=Finset.univ\Z) (hZ:(Z.card:ℝ)≤ε*Fintype.card V)
    (hW:W.card≤f) (hB:(B.card:ℝ)≤γ)
    (hWbudget:f+l*a≤f₀) (hBbudget:γ+l*b≤ε*Fintype.card V+f₀)
    (G:Fin l→SimpleGraph V) (Hs:Fin l→V→U→Prop)
    (hsize:∀i,(ordinaryPhysicalGraph (G i) (Hs i)).support.toFinset.card≤m)
    (hbalance:∀i v,(G i).degree v=2*(Finset.univ.filter (Hs i v)).card)
    (hdiv:∀i u,r∣(Finset.univ.filter (fun v=>Hs i v u)).card)
    (hG:∀i,G i≤rawWheelGraph P σ\F)
    (hH:∀i v u,Hs i v u→ rawWheelSpokes π d σ j v u)
    (hrows:∀i,(G i).support.toFinset⊆W)
    (hactive:∀i u,(∃v,Hs i v u)→u∈B)
    (hAbs:∀(G':SimpleGraph V) (H':V→U→Prop) (A' Z' W':Finset V) (B':Finset U),
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤rawWheelGraph P σ\F → (∀v u,H' v u→ rawWheelSpokes π d σ j v u) →
      (∀u,(∃v,H' v u)→u∈B') →
      A'=Finset.univ\Z' → (Z'.card:ℝ)≤ε*Fintype.card V → W'.card≤f₀ →
      (B'.card:ℝ)≤ε*Fintype.card V+f₀ →
      ∃C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=rawWheelGraph P σ\F) (F:=F)
          (Hbase:=rawWheelSpokes π d σ j) (r:=r)) (ordinaryHostResources G' H') C ∧
        C⊆ordinaryHostResources (rawWheelGraph P σ\F) (rawWheelSpokes π d σ j) ∧
        (ordinaryResourceRows C).card≤a ∧ (ordinaryResourceHubs C).card≤b ∧
        ordinaryResourceRows C⊆G'.support.toFinset∪A' ∧
        (∀v∈ordinaryResourceRows C,v∈W'→v∈G'.support.toFinset) ∧
        (∀u∈ordinaryResourceHubs C,u∈B'→u∈Finset.univ.filter (fun u=>∃v,H' v u)) ∧
        Disjoint C (ordinaryRootResources W' B')):
    ∃C:Finset (Sym2 V⊕(V×U)),
      C⊆ordinaryHostResources (rawWheelGraph P σ\F) (rawWheelSpokes π d σ j) ∧
      Disjoint C (ordinaryRootResources W B) ∧
      (ordinaryResourceRows C).card≤l*a ∧ (ordinaryResourceHubs C).card≤l*b ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=rawWheelGraph P σ\F) (F:=F)
        (Hbase:=rawWheelSpokes π d σ j) (r:=r)) C ∧
      ∀i,IsResourceAbsorber (ordinaryWheelResources (P:=rawWheelGraph P σ\F) (F:=F)
        (Hbase:=rawWheelSpokes π d σ j) (r:=r)) (ordinaryHostResources (G i) (Hs i)) C:=by
  apply ordinary_uniform_terminal_reservoir r m l f a b f₀ γ ε (rawWheelGraph P σ\F) F
    (rawWheelSpokes π d σ j) W B hW hB hWbudget hBbudget G Hs hsize hbalance hdiv hG hH hrows hactive
  intro G' H' W' B' hs hb hd hg hh ha hw hb'
  obtain ⟨C,hC,hhost,hr,hu,_,_,_,hdisj⟩:=hAbs G' H' A Z W' B' hs hb hd hg hh ha hA hZ hw hb'
  exact ⟨C,hC,hhost,hr,hu,hdisj⟩
end Oberwolfach
