module

public import Oberwolfach.OrdinaryAllTerminalReservoir

@[expose] public section
/-! The uniform sampled absorber event gives one reservoir for every
admissible remainder on the terminal row/hub pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_all_terminal_reservoir_from_sample_event
    (r m f a b f₀:ℕ) (γ ε:ℝ) (Q F:SimpleGraph V) (H:V→U→Prop)
    (A Z Wterm W:Finset V) (Bterm B:Finset U)
    (hA:A=Finset.univ\Z) (hZ:(Z.card:ℝ)≤ε*Fintype.card V)
    (hWW:Wterm⊆W) (hBB:Bterm⊆B) (hW:W.card≤f) (hB:(B.card:ℝ)≤γ)
    (L:ℕ) (hL:2^(Wterm.card*Wterm.card+Wterm.card*Bterm.card)≤L)
    (hWbudget:f+L*a≤f₀) (hBbudget:γ+L*b≤ε*Fintype.card V+f₀)
    (hAbs:∀(G':SimpleGraph V) (H':V→U→Prop) (A' Z' W':Finset V) (B':Finset U),
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤Q → (∀v u,H' v u→ H v u) →
      (∀u,(∃v,H' v u)→u∈B') →
      A'=Finset.univ\Z' → (Z'.card:ℝ)≤ε*Fintype.card V → W'.card≤f₀ →
      (B'.card:ℝ)≤ε*Fintype.card V+f₀ →
      ∃C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F)
          (Hbase:=H) (r:=r)) (ordinaryHostResources G' H') C ∧
        C⊆ordinaryHostResources (Q) (H) ∧
        (ordinaryResourceRows C).card≤a ∧ (ordinaryResourceHubs C).card≤b ∧
        ordinaryResourceRows C⊆G'.support.toFinset∪A' ∧
        (∀v∈ordinaryResourceRows C,v∈W'→v∈G'.support.toFinset) ∧
        (∀u∈ordinaryResourceHubs C,u∈B'→u∈Finset.univ.filter (fun u=>∃v,H' v u)) ∧
        Disjoint C (ordinaryRootResources W' B')):
    ∃C:Finset (Sym2 V⊕(V×U)),C⊆ordinaryHostResources Q H ∧
      Disjoint C (ordinaryRootResources W B) ∧
      (ordinaryResourceRows C).card≤L*a ∧ (ordinaryResourceHubs C).card≤L*b ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) C ∧
      ∀(G:SimpleGraph V) (Hs:V→U→Prop),
        ordinaryHostResources G Hs⊆ordinaryRootResources Wterm Bterm →
        (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m →
        (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
        (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) →
        G≤Q → (∀v u,Hs v u→H v u) →
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G Hs) C:=by
  apply ordinary_all_terminal_reservoir r m f a b f₀ γ ε Q F H Wterm W Bterm B
    hWW hBB hW hB L hL hWbudget hBbudget
  intro G Hs W' B' hs hb hd hg hh ha hw hb'
  obtain ⟨C,hC,hhost,hr,hu,_,_,_,hdisj⟩:=hAbs G Hs A Z W' B' hs hb hd hg hh ha hA hZ hw hb'
  exact ⟨C,hC,hhost,hr,hu,hdisj⟩
end Oberwolfach
