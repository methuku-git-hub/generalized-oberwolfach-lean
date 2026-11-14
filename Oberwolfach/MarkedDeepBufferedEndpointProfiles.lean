module

public import Oberwolfach.MarkedDeepEndpointProfiles
public import Oberwolfach.MarkedEndpointBufferNumerics

@[expose] public section

/-! Fixed-profile endpoint blocks with the degree and cut reserves needed
by successive row covers. The error tolerance still precedes d. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_deep_buffered_endpoint_profiles
    (omega t rho eta:ℝ) (ho:0<omega) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1)
    (c:ℕ) (hc:4≤c) (hst:((c:ℝ)-1)*t≤1)
    (heta:0<eta) (hetaSmall:eta≤t*(t*omega/2)/32):
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
    (∀ mark incoming x,(t*omega/2)*n≤
      ((markedEndpointLabels P π d A (mark,incoming,x) σ').card:ℝ)) ∧
    (∀ r x,(t*omega/2)*n≤((B.filter (H' r x)).card:ℝ)) ∧
    (∀ x,((markedEndpointLabels P π d A (true,false,x) σ').card:ℝ)+2*(eta*n)≤
      (B.filter (H' false x)).card) ∧
    (∀ (root:Bool×Bool×V) (r typ:Bool) (loss:ℝ),loss≤(t*(t*omega/2)/4)*n→
      BipartiteBlockBounds (H' typ) (fun z=>z∈markedEndpointLabels P π d A root σ')
        (fun u=>u∈B.filter (H' r root.2.2)) ((t*(t*omega/2)/4)*n+loss) (eta*n) (2*(t/4))) ∧
    2*(eta*n)+(2*(2*(3*d)+1):ℕ)≤(t*(t*omega/2)/4)*n ∧
    (2*(2*(3*d)+1):ℕ)<(t/4)*(eta*n):=by
  have ha:0<t*omega/2:=by positivity
  have hsmall:eta≤t*(t*omega/2)/8:=by
    have hp:0<t*(t*omega/2):=mul_pos ht ha
    linarith only [hetaSmall,hp]
  obtain ⟨eps,heps,hprofiles⟩:=marked_deep_endpoint_profiles omega t rho eta ho ht hrho hrho1 c hc hst heta hsmall
  refine ⟨eps,heps,?_⟩
  intro d
  obtain ⟨N₀,hN₀,hprofile⟩:=hprofiles d
  obtain ⟨N₁,hN₁⟩:=marked_endpoint_buffer_numerics t (t*omega/2) eta ht ha heta hetaSmall d
  refine ⟨max N₀ N₁,hN₀.trans (le_max_left _ _),?_⟩
  intro n hn V U Γ Color _ _ _ _ _ _ hVn P π h hh A B hA hBn hBn1 q s g j hq hs
    errR errI deltaR deltaV deltaU deltaP hR hI hdR hdV hdU hdP htolR htolI htolP hparent
    σ H hr hi DR DS hDR hDSV hDSU
  dsimp only
  obtain ⟨hL,hY,hgap,hblocks,_,_⟩:=hprofile n ((le_max_left _ _).trans hn) V U Γ Color hVn P π h hh A B hA hBn hBn1
    q s g j hq hs errR errI deltaR deltaV deltaU deltaP hR hI hdR hdV hdU hdP htolR htolI htolP
    hparent σ H hr hi DR DS hDR hDSV hDSU
  obtain ⟨hdeg,hmargin,hloss⟩:=hN₁ n ((le_max_right _ _).trans hn)
  refine ⟨hL,hY,hgap,?_,hdeg,hmargin⟩
  intro root r typ loss hsmallLoss
  have hb:=bipartite_block_weaken_degree _ _ _ _ _ _ _ (hblocks root r typ) (hloss loss hsmallLoss)
  convert hb using 1 <;> ring

end Oberwolfach
