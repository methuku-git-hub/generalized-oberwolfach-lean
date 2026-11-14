module

public import Oberwolfach.MarkedEndpointBlocksAfterDeletion
public import Oberwolfach.MarkedEndpointClassSizes

@[expose] public section

/-! The deep-row endpoint inputs from the actual parent degrees and fixed
profiles. Class sizes, the pairing gap, and degree/cut bounds are all derived.
The allowable profile/deletion error precedes d; only N depends on d. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_deep_endpoint_profiles_uniform
    (omega₀ t₀ eta:ℝ) (ho₀:0<omega₀) (ht₀:0<t₀) (ht₀1:t₀≤1)
    (c:ℕ) (hc:4≤c)
    (heta:0<eta) (hetaSmall:eta≤t₀*(t₀*omega₀/2)/8):
    ∃ eps:ℝ,0<eps ∧ ∀ d:ℕ,∃ N:ℕ,1≤N ∧ ∀ n:ℕ,N≤n→
    ∀ omega t rho:ℝ,omega₀≤omega → t₀≤t → 0<rho → rho≤1 → ((c:ℝ)-1)*t≤1 →
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
    (∀ (root:Bool×Bool×V) (r typ:Bool),
      BipartiteBlockBounds (H' typ) (fun z=>z∈markedEndpointLabels P π d A root σ')
        (fun u=>u∈B.filter (H' r root.2.2)) ((t₀*(t₀*omega₀/2)/2)*n) (eta*n) (t₀/2)) ∧
    2*(eta*n)+(2*(2*(3*d)+1):ℕ)≤(t₀*(t₀*omega₀/2)/2)*n ∧
    (2*(2*(3*d)+1):ℕ)<(t₀/2)*(eta*n):=by
  have hc':(4:ℝ)≤c:=by exact_mod_cast hc
  obtain ⟨eps₀,heps₀,hblocks⟩:=marked_endpoint_blocks_after_deletion t₀ (t₀*omega₀/2) eta
    ht₀ ht₀1 (by positivity) heta hetaSmall
  let eps:=min eps₀ (t₀*omega₀/32)
  have heps:0<eps:=lt_min heps₀ (by positivity)
  have hep0:eps≤eps₀:=min_le_left _ _
  have hepsmall:eps≤t₀*omega₀/32:=min_le_right _ _
  refine ⟨eps,heps,?_⟩
  intro d
  obtain ⟨N₀,hN₀,hblock⟩:=hblocks d
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (16*(6*(d:ℝ)+1)/(t₀*omega₀))
  refine ⟨max N₀ N₁,hN₀.trans (le_max_left _ _),?_⟩
  intro n hn omega t rho hω htlo hrho hrho1 hst
  have ho:0<omega:=ho₀.trans_le hω
  have ht:0<t:=ht₀.trans_le htlo
  have ht1:t≤1:=by nlinarith only [hst,hc',ht]
  have hprod:t₀*omega₀≤t*omega:=mul_le_mul htlo hω ho₀.le ht.le
  have hetaSmall':eta≤t*(t*omega/2)/8:=by
    have hp:=mul_le_mul htlo hprod (mul_nonneg ht₀.le ho₀.le) ht.le
    nlinarith only [hetaSmall,hp]
  intro V U Γ Color _ _ _ _ _ _ hVn P π h hh A B hA hBn hBn1 q s g j hq hs
    errR errI deltaR deltaV deltaU deltaP hR hI hdR hdV hdU hdP htolR htolI htolP hparent
    σ H hr hi DR DS hDR hDSV hDSU
  try dsimp only
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg n
  have htoleps:eps*n≤eps₀*n:=mul_le_mul_of_nonneg_right hep0 hn0
  have htols0:eps*n≤(t₀*omega₀/32)*n:=mul_le_mul_of_nonneg_right hepsmall hn0
  have htols:eps*n≤(t*omega/32)*n:=by nlinarith [mul_nonneg (sub_nonneg.mpr hprod) hn0]
  have hdn0:16*(6*(d:ℝ)+1)<(n:ℝ)*(t₀*omega₀):=by
    apply (div_lt_iff₀ (mul_pos ht₀ ho₀)).mp
    exact hN₁.trans_le (Nat.cast_le.mpr ((le_max_right _ _).trans hn))
  have hdn:16*(6*(d:ℝ)+1)<(n:ℝ)*(t*omega):=by nlinarith [mul_nonneg (sub_nonneg.mpr hprod) hn0]
  have herrR:errR+h*(deltaR+deltaU)+(6*(d:ℝ)+1)+deltaP≤t*omega*n/4:=by
    nlinarith only [htolR,htolP,htols,hdn]
  have herrI:errI+h*deltaV≤t*omega*n/4:=by
    have hp:0≤t*omega*n:=mul_nonneg (mul_pos ht ho).le hn0
    nlinarith only [htolI,htols,hp]
  have heta':eta≤t*omega/8:=by
    have hp:0<t*omega:=mul_pos ht ho
    have hm:=mul_le_mul_of_nonneg_right ht1 hp.le
    nlinarith only [hetaSmall',hm,hp]
  obtain ⟨hr',hi'⟩:=marked_neighbourhoods_after_physical_deletion P π d h A B
    (rho*(((c:ℝ)-1)*t)/2) (rho*t/2) q s g j errR errI deltaR deltaV deltaU hdR hdV hdU
    σ H hr hi DR DS hDR hDSV hDSU
  obtain ⟨hL,hY,hgap⟩:=marked_endpoint_class_sizes P π d h hh A B hA n omega t rho
    ho ht hrho hrho1 c hc hst hBn q s g j hq hs
    (errR+h*(deltaR+deltaU)) (errI+h*deltaV) deltaP eta
    (by positivity) (by positivity) hdP hparent herrR herrI heta' _ _ hr' hi'
  have hw:∀ typ:Bool,t≤(if typ then t else ((c:ℝ)-1)*t) ∧
      (if typ then t else ((c:ℝ)-1)*t)≤1:=by
    intro typ
    cases typ
    · simp only [Bool.false_eq_true,ite_false]
      exact ⟨by nlinarith only [hc',ht],hst⟩
    · exact ⟨le_rfl,ht1⟩
  have hall:=hblock n ((le_max_left _ _).trans hn) V U Γ Color P π h hh A B
    (rho*(((c:ℝ)-1)*t)/2) (rho*t/2) q s g j errR errI deltaR deltaV deltaU
    hR hI hdR hdV hdU (htolR.trans htoleps) (htolI.trans htoleps) σ H hr hi DR DS hDR hDSV hDSU
    (fun typ=>if typ then t else ((c:ℝ)-1)*t) hq hs (fun typ=>⟨htlo.trans (hw typ).1,(hw typ).2⟩)
  have hall':∀ root:Bool×Bool×V,∀ r typ:Bool,
      BipartiteBlockBounds (markedDeletePhysicalSpokes H DS typ)
        (fun z=>z∈markedEndpointLabels P π d A root (rawMarkedDeleteRims σ DR.edgeFinset))
        (fun u=>u∈B.filter (markedDeletePhysicalSpokes H DS r root.2.2))
        ((t₀*(t₀*omega₀/2)/2)*n) (eta*n) (t₀/2) ∧
      2*(eta*n)+(2*(2*(3*d)+1):ℕ)≤(t₀*(t₀*omega₀/2)/2)*n ∧
      (2*(2*(3*d)+1):ℕ)<(t₀/2)*(eta*n):=by
    intro root r typ
    have ha:(t₀*omega₀/2)*n≤(t*omega/2)*n:=by nlinarith [mul_nonneg (sub_nonneg.mpr hprod) hn0]
    apply hall root r typ (ha.trans (hL root.1 root.2.1 root.2.2)) (ha.trans (hY r root.2.2))
    exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans hBn1
  refine ⟨hL,hY,hgap,fun root r typ=>(hall' root r typ).1,?_⟩
  have hnp:0<n:=lt_of_lt_of_le Nat.zero_lt_one (hN₀.trans ((le_max_left _ _).trans hn))
  have hv:Nonempty V:=Fintype.card_pos_iff.mp (by omega)
  let x:V:=Classical.choice hv
  exact (hall' (false,false,x) false false).2

end Oberwolfach
