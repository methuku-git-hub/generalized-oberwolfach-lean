module

public import Oberwolfach.PhysicalBoundaryClassSizeEvent
public import Oberwolfach.MarkedBoundaryClassSizeMargins

@[expose] public section

/-! One physical sampling event supplies all class-size and pairing-gap
margins for every later class differing by the permitted realized loss.
Only the original parent classes are fixed before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_boundary_class_margins_event (a g:ℝ) (ha:0<a) (hg:0<g) (q:ℕ):
    ∃ pmax:ℝ,0<pmax∧pmax≤1∧∀ p:ℝ,0<p→p≤pmax→∃ N:ℕ,
    ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
    N≤Fintype.card (V⊕U)→∀ (π:Equiv.Perm V) (roots:Finset V)
      (L:Bool→Bool→V→Finset V) (B:Bool→V→Finset U),
    (∀ mark incoming x,x∈roots→a*Fintype.card (V⊕U)≤((L mark incoming x).card:ℝ))→
    (∀ b x,x∈roots→a*Fintype.card (V⊕U)≤((B b x).card:ℝ))→
    (∀ x,x∈roots→((L true false x).card:ℝ)+g*Fintype.card (V⊕U)≤(B false x).card)→
    ∀ (hp:0≤p) (hp1:p≤1),
    1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp hp1)).probability (fun σ=>
      ∀ (L':Bool→Bool→V→Finset V) (B':Bool→V→Finset U),
      (∀ mark incoming x,x∈roots→((changed (L' mark incoming x)
        ((L mark incoming x).filter (fun v=>σ (markedBoundaryEndpointCoin π mark incoming x (Sum.inl v))=true))).card:ℝ)≤
          (p^9+p^3)*Fintype.card (V⊕U))→
      (∀ b x,x∈roots→((changed (B' b x) ((B b x).filter (fun u=>σ s(Sum.inl x,Sum.inr u)=true))).card:ℝ)≤
          (p^9+p^3)*Fintype.card (V⊕U))→
      (∀ mark incoming x,x∈roots→(a/2)*p*Fintype.card (V⊕U)≤((L' mark incoming x).card:ℝ)∧
        ((L' mark incoming x).card:ℝ)≤2*p*Fintype.card (V⊕U))∧
      (∀ b x,x∈roots→(a/2)*p*Fintype.card (V⊕U)≤((B' b x).card:ℝ)∧
        ((B' b x).card:ℝ)≤2*p*Fintype.card (V⊕U))∧
      (∀ x,x∈roots→((L' true false x).card:ℝ)+(g/2)*p*Fintype.card (V⊕U)≤(B' false x).card)):=by
  obtain ⟨η,pmax,hη,hpmax,hpmax1,hnum⟩:=marked_boundary_class_size_margins a g ha hg
  refine ⟨pmax,hpmax,hpmax1,?_⟩
  intro p hp hpp
  obtain ⟨N,hN⟩:=physical_boundary_class_size_event (η*p) (mul_pos hη hp) q
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn π roots L B hL hB hgap hp' hp1
  have hevent:=hN V U hn π L B (fun _=>∅) p hp' hp1
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ L' B' hL' hB'
  have h:=hnum p hp hpp (Fintype.card (V⊕U))
  have hLV (mark incoming:Bool) (x:V):((L mark incoming x).card:ℝ)≤Fintype.card (V⊕U):=by
    exact_mod_cast (Finset.card_le_univ (L mark incoming x)).trans (by simp [Fintype.card_sum])
  have hBU (b:Bool) (x:V):((B b x).card:ℝ)≤Fintype.card (V⊕U):=by
    exact_mod_cast (Finset.card_le_univ (B b x)).trans (by simp [Fintype.card_sum])
  refine ⟨?_,?_,?_⟩
  · intro mark incoming x hx
    exact h.1 (L mark incoming x) _ (L' mark incoming x) (hL mark incoming x hx) (hLV mark incoming x)
      (hσ.1 mark incoming x) (hL' mark incoming x hx)
  · intro b x hx
    exact h.1 (B b x) _ (B' b x) (hB b x hx) (hBU b x) (hσ.2.1 b x) (hB' b x hx)
  · intro x hx
    exact h.2 (B false x) _ (B' false x) (L true false x) _ (L' true false x)
      (hgap x hx) (hσ.2.1 false x) (hσ.1 true false x) (hB' false x hx) (hL' true false x hx)
end Oberwolfach
