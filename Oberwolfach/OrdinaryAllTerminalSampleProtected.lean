module

public import Oberwolfach.OrdinaryAllTerminalReservoirRows
public import Oberwolfach.OrdinaryReservoirInnerProtection

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

theorem ordinary_all_terminal_reservoir_protecting_inner_pair
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
      Disjoint C (ordinaryRootResources Z B) ∧
      (ordinaryResourceRows C).card≤L*a ∧ (ordinaryResourceHubs C).card≤L*b ∧
      ordinaryResourceRows C⊆Wterm∪A ∧ HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) C ∧
      ∀(G:SimpleGraph V) (Hs:V→U→Prop),
        ordinaryHostResources G Hs⊆ordinaryRootResources Wterm Bterm →
        (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m →
        (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
        (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) →
        G≤Q → (∀v u,Hs v u→H v u) →
        IsResourceAbsorber (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
          (ordinaryHostResources G Hs) C :=by
  have hh:=ordinary_all_terminal_reservoir_rows r m f a b f₀ γ ε Q F H A Wterm W Bterm B
    hWW hBB hW hB L hL hWbudget hBbudget (by
      intro G Hs W' B' hs hb hd hg hh ha hw hb'
      obtain ⟨C,hC,hhost,hr,hu,hrows,_,_,hdisj⟩:=hAbs G Hs A Z W' B' hs hb hd hg hh ha hA hZ hw hb'
      exact ⟨C,hC,hhost,hr,hu,hrows,hdisj⟩)
  obtain ⟨C,hhost,havoid,hr,hu,hrows,hdec,habs⟩:=hh
  have hroot:ordinaryRootResources Wterm B⊆ordinaryRootResources W B:=
    ordinaryRootResources_contains _ _ _
      ((ordinaryRootResources_rows Wterm B).trans hWW) (ordinaryRootResources_hubs Wterm B)
  have hprotected:Disjoint C (ordinaryRootResources Z B):=by
    apply ordinary_reservoir_protects_inner_pair C Wterm Z B
    · simpa only [hA] using hrows
    · exact havoid.mono_right hroot
  exact ⟨C,hhost,hprotected,hr,hu,hrows,hdec,habs⟩
end Oberwolfach
