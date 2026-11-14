module

public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion
public import Oberwolfach.MarkedEndpointBlockNumerics

@[expose] public section

/-! Actual endpoint degree and cut bounds after a later physical deletion.
The profile tolerance is chosen before the separation radius. All modified
neighbourhoods are computed from the supplied outcome and deletion graphs;
the new degree/cut properties are conclusions rather than caller inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_endpoint_blocks_after_deletion
    (p₀ a eta:ℝ) (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (heta:0<eta)
    (hetaSmall:eta≤p₀*a/8):
    ∃ eps:ℝ,0<eps ∧ ∀ d:ℕ,∃ N:ℕ,1≤N ∧ ∀ n:ℕ,N≤n→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (h:ℕ),3≤h→
    ∀ (A:Finset V) (B:Finset U) (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
      (errR errI deltaR deltaV deltaU:ℝ),
    0≤errR→0≤errI→0≤deltaR→0≤deltaV→0≤deltaU→
    errR+h*(deltaR+deltaU)≤eps*n→errI+h*deltaV≤eps*n→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d h A p k q s g j errR σ H→
    MarkedIndicesWithSpokes π d h B q s g j errI σ H→
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ x,(DR.degree x:ℝ)≤deltaR)→
    (∀ x,(DS.degree (Sum.inl x):ℝ)≤deltaV)→
    (∀ u,(DS.degree (Sum.inr u):ℝ)≤deltaU)→
    ∀ w:Bool→ℝ,(∀ u∈B,q u g=w true)→(∀ u∈B,s u j=w false)→
    (∀ t,p₀≤w t ∧ w t≤1)→
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    ∀ (root:Bool×Bool×V) (r t:Bool),
    a*n≤((markedEndpointLabels P π d A root σ').card:ℝ)→
    a*n≤((B.filter (H' r root.2.2)).card:ℝ)→
    ((B.filter (H' r root.2.2)).card:ℝ)≤n→
    BipartiteBlockBounds (H' t) (fun z=>z∈markedEndpointLabels P π d A root σ')
      (fun u=>u∈B.filter (H' r root.2.2)) ((p₀*a/2)*n) (eta*n) (p₀/2) ∧
    2*(eta*n)+(2*(2*(3*d)+1):ℕ)≤(p₀*a/2)*n ∧
    (2*(2*(3*d)+1):ℕ)<(p₀/2)*(eta*n):=by
  obtain ⟨eps,e,heps,he,hnum⟩:=marked_endpoint_block_numeric_threshold p₀ a eta hp₀ hp₀1 ha heta hetaSmall
  refine ⟨eps,heps,?_⟩
  intro d
  obtain ⟨N,hN⟩:=hnum d
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn V U Γ Color _ _ _ _ _ _ P π h hh A B p k q s g j
    errR errI deltaR deltaV deltaU hR hI hdR hdV hdU htolR htolI σ H hr hi
    DR DS hDR hDSV hDSU w hq hs hw
  dsimp only
  intro root r t hL hY hYn
  let σ':=rawMarkedDeleteRims σ DR.edgeFinset
  let H':=markedDeletePhysicalSpokes H DS
  have hn':N≤n:=(le_max_left _ _).trans hn
  have hnp:(0:ℝ)<n:=by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hn))
  have hYp:0<(B.filter (H' r root.2.2)).card:=by
    have hp:0<((B.filter (H' r root.2.2)).card:ℝ):=(mul_pos ha hnp).trans_le hY
    exact_mod_cast hp
  obtain ⟨hr',hi'⟩:=marked_neighbourhoods_after_physical_deletion P π d h A B p k q s g j
    errR errI deltaR deltaV deltaU hdR hdV hdU σ H hr hi DR DS hDR hDSV hDSU
  obtain ⟨hrelR,hrelI,hsmall,hlarge,hdL,hdY,htau,hlam,hdeg,hmargin⟩:=
    hN n hn' (markedEndpointLabels P π d A root σ').card (B.filter (H' r root.2.2)).card
      hL hY hYn (w t) (hw t).1 (hw t).2
  have hb:=marked_endpoint_block_bounds P π d h hh A B p k q s g j
    (errR+h*(deltaR+deltaU)) (errI+h*deltaV) e eta ((p₀*a/2)*n) (eta*n) (p₀/2)
    (by positivity) (by positivity) he.le heta σ' H' hr' hi' w hq hs
    (fun t=>⟨hp₀.trans_le (hw t).1,(hw t).2⟩) root r t hYp
    (by linarith only [hrelR,htolR]) (by linarith only [hrelI,htolI])
    hsmall hlarge hdY hdL htau hlam
  exact ⟨hb,hdeg,hmargin⟩

end Oberwolfach
