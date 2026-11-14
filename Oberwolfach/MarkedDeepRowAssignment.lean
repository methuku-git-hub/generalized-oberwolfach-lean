module

public import Oberwolfach.MarkedDeepEndpointProfiles
public import Oberwolfach.MarkedEndpointPairingConstruction

@[expose] public section

/-! Construct the two compatible endpoint bijections in the actual deleted
host from its parent degrees and original fixed profiles. No matching,
endpoint cut bound, degree bound, class-size bound or separation margin
is supplied as an assumption. The three local cardinal balances remain
explicit: they are consequences of local marked divisibility. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_deep_row_assignment
    (omega t rho eta:ℝ) (ho:0<omega) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1)
    (c:ℕ) (hc:4≤c) (hst:((c:ℝ)-1)*t≤1)
    (heta:0<eta) (hetaSmall:eta≤t*(t*omega/2)/8):
    ∃ eps:ℝ,0<eps ∧ ∀ d:ℕ,∃ N:ℕ,1≤N ∧ ∀ n:ℕ,N≤n→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    Fintype.card V=n→∀ (P:SimpleGraph V) (π:Equiv.Perm V) (h:ℕ),3≤h→
    ∀ (A:Finset V) (B:Finset U),(∀ x,π x∈A↔x∈A)→ omega*n≤(B.card:ℝ)→(B.card:ℝ)≤n→
    ∀ (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color),
    (∀ u∈B,q u g=t)→(∀ u∈B,s u j=((c:ℝ)-1)*t)→
    ∀ errR errI deltaR deltaV deltaU deltaP:ℝ,
    0≤errR→0≤errI→0≤deltaR→0≤deltaV→0≤deltaU→0≤deltaP→
    errR+h*(deltaR+deltaU)≤eps*n→errI+h*deltaV≤eps*n→deltaP≤eps*n→
    (∀ x,|((P.neighborFinset x∩A).card:ℝ)-2*B.card/rho|≤deltaP)→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d h A (rho*(((c:ℝ)-1)*t)/2) (rho*t/2) q s g j errR σ H→
    MarkedIndicesWithSpokes π d h B q s g j errI σ H→
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ x,(DR.degree x:ℝ)≤deltaR)→
    (∀ x,(DS.degree (Sum.inl x):ℝ)≤deltaV)→
    (∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaU)→
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    ∀ x:V,
    let A₀:=markedEndpointLabels P π d A (false,true,x) σ'
    let A₁:=markedEndpointLabels P π d A (true,true,x) σ'
    let X₀:=markedEndpointLabels P π d A (false,false,x) σ'
    let X₁:=markedEndpointLabels P π d A (true,false,x) σ'
    let Y₀:=B.filter (H' false x)
    let Y₁:=B.filter (H' true x)
    (∀ u,¬(H false x u ∧ H true x u))→
    A₀.card+A₁.card=Y₀.card+Y₁.card→
    X₀.card+X₁.card=Y₀.card+Y₁.card→A₁.card=Y₁.card→
    Nonempty (MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ (H' false) (H' true) π (3*d)):=by
  obtain ⟨eps,heps,hprofiles⟩:=marked_deep_endpoint_profiles omega t rho eta ho ht hrho hrho1 c hc hst heta hetaSmall
  refine ⟨eps,heps,?_⟩
  intro d
  obtain ⟨N,hN,hprofile⟩:=hprofiles d
  refine ⟨N,hN,?_⟩
  intro n hn V U Γ Color _ _ _ _ _ _ hVn P π h hh A B hA hBn hBn1 q s g j hq hs
    errR errI deltaR deltaV deltaU deltaP hR hI hdR hdV hdU hdP htolR htolI htolP hparent
    σ H hr hi DR DS hDR hDSV hDSU
  dsimp only
  intro x hdis hbalA hbalX hmarked
  obtain ⟨_,_,hgap,hblocks,hdegree,hmargin⟩:=hprofile n hn V U Γ Color hVn P π h hh A B hA hBn hBn1
    q s g j hq hs errR errI deltaR deltaV deltaU deltaP hR hI hdR hdV hdU hdP htolR htolI htolP
    hparent σ H hr hi DR DS hDR hDSV hDSU
  have hdis':Disjoint (B.filter (markedDeletePhysicalSpokes H DS false x))
      (B.filter (markedDeletePhysicalSpokes H DS true x)):=by
    apply Finset.disjoint_left.mpr
    intro u hu hu'
    exact hdis u ⟨(Finset.mem_filter.mp hu).2.1,(Finset.mem_filter.mp hu').2.1⟩
  have hnp:(0:ℝ)<n:=by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hN.trans hn))
  exact marked_endpoint_pairing_from_blocks _ _ _ _ _ _ hdis' _ _ π (3*d)
    hbalA hbalX hmarked ((t*(t*omega/2)/2)*n) (eta*n) (t/2) (mul_pos heta hnp) (by positivity)
    hdegree hmargin (hgap x)
    (hblocks (true,true,x) true false) (hblocks (false,true,x) false false)
    (hblocks (true,false,x) false true) (hblocks (false,false,x) false false)
    (hblocks (false,false,x) true false)

end Oberwolfach
