module

public import Oberwolfach.MarkedNearBalancePacking
public import Oberwolfach.OrderedCanonicalCommonPaths
public import Oberwolfach.ConstantSpokeIntersections

@[expose] public section

/-! Numerical marked near-balance packing with the manuscript's root-first
common-path counts and physical edge-load tests. The density profiles are
constant within each spoke type, and remain fixed through correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_near_balance_wheel_packing_numerical (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 → ∀ pstar β bminus bplus ω h δ : ℝ,
    0<pstar → 0<β → 0<bminus → 0<bplus → 0<ω → 0<h → 0<δ → δ<1/4 →
    ∃ ε η₀ δ₀ : ℝ,0<ε ∧ 0<η₀ ∧ 0<δ₀ ∧
    ∀ γ : ℝ,0<γ → ∃ ηbal : ℝ,0<ηbal ∧ ∀ b : ℕ,∃ n₀ : ℕ,
    ∀ η : ℝ,0≤η → η≤ηbal →
    ∀ (V E K U : Type)
      [Fintype V] [Fintype E] [Fintype K] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π) →
    ∀ (p D : ℝ),p₀≤p → p≤1/2 → n₀≤Fintype.card V →
    (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ x,|occurrenceDegree tail x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree head x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree ktail x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree khead x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x y,x≠y → 2*α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      2*(α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ H₀ Hₖ : V → U → Prop,
    (∀ v u,¬(H₀ v u ∧ Hₖ v u)) →
    (∀ C' : MarkedCycleTuple tail head ktail khead (k+1) π b,
      2*β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u}:ℝ)) →
    ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (varsigma : Bool → ℝ) (δsp Dexc : ℝ),
    (∀ j,pstar≤varsigma j ∧ varsigma j≤1) → 0≤δsp → 0≤Dexc →
    (∀ j,∀ S : Finset U,1≤S.card → S.card≤3 →
      |((commonSpokeNeighbours (if j then Hₖ else H₀) S).card:ℝ)-
        (varsigma j)^S.card*Fintype.card V|≤δsp*Fintype.card V) →
    (∀ j x,∃ E' : Finset V,(E'.card:ℝ)≤Dexc ∧ ∀ y,y∉E' →
      |((Finset.univ.filter (fun u=>(if j then Hₖ x u else H₀ x u) ∧
        (if j then Hₖ y u else H₀ y u))).card:ℝ)-(varsigma j)^2*Fintype.card U|≤
        δsp*(varsigma j)^2*Fintype.card U) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    (∀ u u' : U,u≠u' → 2*β*(Fintype.card V:ℝ)^(k+2)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (k+1) π b H₀ Hₖ u u'):ℝ)) →
    (∀ j,∀ Q : BipartiteFourCycle (if j then Hₖ else H₀),
      2*β*(Fintype.card V:ℝ)^(k+1)≤
      (Fintype.card (RootFirstCommonMarkedPath tail head ktail khead (k+1) π b H₀ Hₖ j
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ)) →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e : E⊕K,|(∑ W,if Sum.inl (markedPhysicalEdge tail head ktail khead π e)∈markedWheelPhysicalResources W
      then ψ W else 0)-1|≤η₀) →
    (∀ v u,H₀ v u ∨ Hₖ v u →
      |(∑ W,if Sum.inr (v,u)∈markedWheelPhysicalResources W then ψ W else 0)-1|≤η₀) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(k+1)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(k+1)) →
    ∀ (A₀ Aₖ : V → V → ℕ) (T₀ Tₖ : V → U → ℕ),
    (∀ x y,A₀ x y≤occurrenceMultiplicity tail head x y) →
    (∀ x y,Aₖ x y≤occurrenceMultiplicity ktail khead x y) →
    (∀ v u,T₀ v u≤relationMultiplicity H₀ v u) →
    (∀ v u,Tₖ v u≤relationMultiplicity Hₖ v u) →
    (∀ v,|occurrenceDegree (Sum.elim tail ktail) v-
      (∑ u,if H₀ v u then (1:ℝ) else 0)-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    (∀ v,|occurrenceDegree (Sum.elim head khead) v-
      (∑ u,if H₀ v u then (1:ℝ) else 0)-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    (∀ v,|occurrenceDegree khead v-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    (∀ u,|(∑ v,if H₀ v u then (1:ℝ) else 0)-(k+1:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    BipartiteLargeCut A₀ δ h → BipartiteLargeCut Aₖ δ h →
    BipartiteLargeCut T₀ δ h → BipartiteLargeCut Tₖ δ h →
    ∃ M : Finset (MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
      (∀ x : V⊕U,((markedIncidentEdges tail head ktail khead π H₀ Hₖ false x \
        M.biUnion markedActiveResources).card : ℝ)≤γ*Fintype.card V) ∧
      (∀ x : V⊕U,((markedPhysicalIncidentEdges tail head ktail khead π H₀ Hₖ x \
        M.biUnion markedWheelPhysicalResources).card : ℝ)≤γ*Fintype.card V) := by
  obtain ⟨c₀,hc₀⟩ := marked_near_balance_wheel_packing α p₀ hα hαmax hp₀ hp₀max
  refine ⟨max c₀ 8,?_⟩
  intro k hk pstar β bminus bplus ω h δ hpstar hβ hbm hbp hω hh hδ hδsmall
  let L := max 1 (1/pstar)
  have hkm : 3<(k+1)+1 := by omega
  obtain ⟨ε,η₀,δ₀,hε,hη₀,hδ₀,hpacking⟩ := hc₀ k ((le_max_left _ _).trans hk)
    β L bminus bplus ω h δ hβ (le_max_left _ _) hbm hbp hω hh hδ hδsmall
  refine ⟨ε,η₀,δ₀,hε,hη₀,hδ₀,?_⟩
  intro γ hγ
  obtain ⟨ηbal,hηbal,hpack⟩ := hpacking γ hγ
  refine ⟨ηbal,hηbal,?_⟩
  intro b
  obtain ⟨N,hN⟩ := hpack b
  refine ⟨N,?_⟩
  intro η hη hηsmall V E K U _ _ _ _ _ _ tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi
    hdo hdi hdko hdki htwo hcut H₀ Hₖ hdisj hhub hωn huV varsigma δsp Dexc hvar hδsp hDexc
    hinter hcodeg hsmall hcommon hpaths ψ hRerr hSerr hψ A₀ Aₖ T₀ Tₖ hA0 hAK hT0 hTK
    hbp0 hbm0 hbk hbw hcut0 hcutK hcutH0 hcutHK
  let i : Bool → Fin (k+2) := fun j=>(markedRootOrder (k+1) j).symm 0
  have hdata (j : Bool) : SparseIntersectionData (if j then Hₖ else H₀)
      (fun _=>varsigma j) (fun _=>1/varsigma j) L δsp Dexc := by
    apply sparseIntersectionData_of_constant_density (if j then Hₖ else H₀)
      (varsigma j) pstar δsp Dexc hpstar (hvar j).1 (hvar j).2 hδsp hDexc (hinter j)
    simpa only [ite_apply] using hcodeg j
  have hcanonical (j : Bool) (Q : BipartiteFourCycle (if j then Hₖ else H₀)) :
      2*β*(Fintype.card V:ℝ)^(k+1)≤
      (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead (k+1) π b H₀ Hₖ (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ) := by
    have hc := rootFirstCommonMarkedPath_canonical_card_le (tail:=tail) (head:=head)
      (ktail:=ktail) (khead:=khead) (m:=k+1) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ)
      j Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2
    exact (hpaths j Q).trans (by
      dsimp only [i]
      simp only [← Nat.card_eq_fintype_card] at hc ⊢
      exact_mod_cast hc)
  have hR (e : E⊕K) : |markedWheelRimLoad ψ e-1|≤η₀ := by
    simpa only [markedWheelPhysicalResources_load_rim hphys] using hRerr e
  have hS : ∀ j v u,|markedSpokeResidual ψ j v u|≤η₀ := by
    apply markedSpokeResidual_of_physical_error hdisj ψ η₀ hη₀.le
    intro v u he
    simpa only [markedWheelPhysicalResources_spoke] using hSerr v u he
  exact hN η hη hηsmall V E K U tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi
    hdo hdi hdko hdki htwo hcut H₀ Hₖ hdisj hhub hωn huV
    (fun j _=>varsigma j) (fun j _=>1/varsigma j) δsp Dexc hdata hsmall i
    (fun j=>markedRootOrder_type (k+1) hkm j) hcommon hcanonical ψ hR hS hψ
    A₀ Aₖ T₀ Tₖ hA0 hAK hT0 hTK hbp0 hbm0 hbk hbw hcut0 hcutK hcutH0 hcutHK

end Oberwolfach
