module

public import Oberwolfach.MarkedFreshEndpointProfiles
public import Oberwolfach.MarkedEndpointFiveBlocks

@[expose] public section

/-! All five actual endpoint blocks use one common physical sampling event.
Repeated classes have the same coordinates, including the two uses of X₀
and each repeated hub class. No independence between blocks is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fresh_five_endpoint_profiles (p₀ a ε:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1) (hε:0<ε):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (d q:ℕ) (ρ:ℝ) (hρ:0<ρ) (hρ1:ρ≤1),∃ N:ℕ,
    ∀ (V U Γ Color I:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      [Fintype Γ] [Fintype Color] [Fintype I],
      N≤Fintype.card (V⊕U)→Fintype.card I≤Fintype.card (V⊕U)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (h:ℕ) (A:Finset V) (B:Finset U)
      (p k:ℝ) (q₀:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j₀:Color)
      (errR errI:ℝ) (σ₀:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
      (w:Bool→ℝ) (root:I→V),
      3≤h→0≤errR→0≤errI→
      2*errR≤η*(a*Fintype.card (V⊕U))→2*errI≤η*(a*Fintype.card (V⊕U))→
      MarkedRowsWithSpokes P π d h A p k q₀ s g j₀ errR σ₀ H→
      MarkedIndicesWithSpokes π d h B q₀ s g j₀ errI σ₀ H→
      (∀ u∈B,q₀ u g=w true)→(∀ u∈B,s u j₀=w false)→
      (∀ e,p₀≤w e ∧ w e≤1)→
    let L:=fun (j:I×Fin 5)=>markedEndpointLabels P π d A (markedEndpointFiveRimType j.2,markedEndpointFiveIncoming j.2,root j.1) σ₀;
    let Y:=fun (j:I×Fin 5)=>B.filter (H (markedEndpointFiveRootSpokeType j.2) (root j.1));
      (∀ j,a*Fintype.card (V⊕U)≤((L j).card:ℝ) ∧ a*Fintype.card (V⊕U)≤((Y j).card:ℝ))→
      1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin ρ hρ.le hρ1)).probability
        (fun σ=>∀ j (A':Finset V) (B':Finset U) (D:SimpleGraph (V⊕U)),A'⊆L j→B'⊆Y j→
          ((changed A' ((L j).filter (fun v=>σ (markedBoundaryEndpointCoin π (markedEndpointFiveRimType j.2) (markedEndpointFiveIncoming j.2) (root j.1) (Sum.inl v))=true))).card:ℝ)≤ζ*(ρ*Fintype.card (V⊕U))→
          ((changed B' ((Y j).filter (fun u=>σ s(Sum.inl (root j.1),Sum.inr u)=true))).card:ℝ)≤ζ*(ρ*Fintype.card (V⊕U))→
          (∀ z,(D.degree z:ℝ)≤ζ*(ρ*Fintype.card (V⊕U)))→
          ρ*(L j).card/2≤(A'.card:ℝ) ∧ ρ*(Y j).card/2≤(B'.card:ℝ) ∧
          ∀ degree tau:ℝ,degree≤p₀/2*A'.card→degree≤p₀/2*B'.card→ε*A'.card≤tau→ε*B'.card≤tau→
          BipartiteBlockBounds (fun v u=>H (markedEndpointFiveLabelSpokeType j.2) v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
            (fun v=>v∈A') (fun u=>u∈B') degree tau (p₀/2)) := by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=marked_fresh_endpoint_profiles p₀ a ε hp₀ hp₀1 ha ha1 hε
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro d q ρ hρ hρ1
  obtain ⟨N,hN⟩:=hbase d q ρ hρ hρ1
  refine ⟨max N 5,?_⟩
  intro V U Γ Color I _ _ _ _ _ _ _ hn hI P π h A B p k q₀ s g j₀
    errR errI σ₀ H w root hh hR hE heR heI hr hi hq hs hw L Y hsize
  have hJ:Fintype.card (I×Fin 5)≤(Fintype.card (V⊕U))^2:=by
    simp only [Fintype.card_prod,Fintype.card_fin]
    have hn5:5≤Fintype.card (V⊕U):=by omega
    nlinarith
  exact hN V U Γ Color (I×Fin 5) (by omega) hJ P π h A B p k q₀ s g j₀ errR errI σ₀ H w
    (fun j=>markedEndpointFiveRimType j.2) (fun j=>markedEndpointFiveIncoming j.2)
    (fun j=>markedEndpointFiveRootSpokeType j.2) (fun j=>markedEndpointFiveLabelSpokeType j.2)
    (fun j=>root j.1) hh hR hE heR heI hr hi hq hs hw hsize

end Oberwolfach
