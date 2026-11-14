module

public import Oberwolfach.SmallSetRowCover
public import Oberwolfach.DomainCodegreeCuts

@[expose] public section

/-! The ordinary successive-row construction from degree and separated
codegree estimates. All tolerances are fixed using a density lower bound,
before the actual density and the forbidden-degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_small_set_row_covers_from_codegrees (r:ℕ) (hr:4≤r) (C₀ β κ p₀:ℝ)
    (hC₀:0≤C₀) (hβ:0<β) (hκ:0<κ) (hp₀:0<p₀) :
    ∃ K:ℕ,0<K ∧ ∃ θ ε:ℝ,0<θ ∧ 0<ε ∧ ∀ d:ℕ,∃ N:ℕ,
      ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      ∀ (Q F:SimpleGraph V) (H:V→U→Prop) (n:ℕ) (x:Fin n→V) (A:Finset V) (p:ℝ),
      N≤A.card → (n:ℝ)≤θ*A.card → p₀≤p → p≤1 → Function.Injective x → (∀ i,x i∉A) →
      (∀ i,Q.neighborFinset (x i)⊆A) →
      let T:=fun i=>Finset.univ.filter (H (x i))
      (∀ i,κ*A.card≤((T i).card:ℝ)) → (∀ i,((T i).card:ℝ)≤C₀*A.card) →
      (∀ i,Q.degree (x i)=2*(T i).card) →
      (∀ a,F.degree a≤d) → (∀ i a,Q.Adj (x i) a → ¬F.Adj (x i) a) →
      (∀ i a,Q.Adj (x i) a → (p-ε)*(T i).card≤(((T i).filter (H a)).card:ℝ)) →
      (∀ i u,u∈T i → p*(T i).card≤(((Q.neighborFinset (x i)).filter (fun a=>H a u)).card:ℝ)) →
      (∀ i a b,Q.Adj (x i) a → Q.Adj (x i) b → a≠b → ¬F.Adj a b →
        (((T i).filter (fun u=>H a u∧H b u)).card:ℝ)≤(p^2+ε)*(T i).card) →
      (∀ i u,u∈T i → ∀ a,a≠x i → ∀ c,c≠x i →
        β*A.card≤(((A.filter (fun z=>H z u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)) →
      ∃ C:Fin n→Finset (OrdinaryWheel Q F H r),
        (∀ i,OrdinaryRowCover (C i) (x i) A K) ∧
        (∀ i j,i≠j → Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)) ∧
        (∀ a∈A,(ordinaryWheelRimGraph (Finset.univ.biUnion C)).degree a≤n*(2*(K+1))) ∧
        (∀ a∈A,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion C) a)).card≤n*(K+1)) ∧
        (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion C) a u)).card≤n*r) := by
  let η:=p₀/64
  have hη:0<η:=by dsimp [η];positivity
  let ε:=min (p₀/2) (p₀^2*η/24)
  have hε:0<ε:=by dsimp [ε];positivity
  obtain ⟨K,hK,θ,hθ,hcover⟩:=ordinary_small_set_row_covers r hr C₀ β κ (p₀/4) hC₀ hβ hκ (by positivity)
  refine ⟨K,hK,θ,ε,hθ,hε,?_⟩
  intro d
  obtain ⟨N₀,hN⟩:=hcover d
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (8*(d+1)/(p₀^2*η^2*κ):ℝ)
  refine ⟨max N₀ (max N₁ 1),?_⟩
  intro V U _ _ _ _ Q F H n x A p hn hnθ hpp hp1 hx hxA hSA T hTlo hThi hbal hF hFx hrow hcol hcodeg hcount
  have ha:(0:ℝ)<A.card:=Nat.cast_pos.mpr (by omega)
  have hp:0<p:=hp₀.trans_le hpp
  have hpp₂:p₀^2≤p^2:=pow_le_pow_left₀ hp₀.le hpp 2
  have hsmall:ε≤p^2*η/24:=by
    have he:ε≤p₀^2*η/24:=min_le_right _ _
    have hh:=mul_le_mul_of_nonneg_right hpp₂ hη.le
    linarith only [he,hh]
  have hmass (i:Fin n):(d+1:ℝ)≤p^2*η^2*(T i).card/8:=by
    have hh:=(div_lt_iff₀ (by positivity:0<p₀^2*η^2*κ)).mp
      (hN₁.trans_le (Nat.cast_le.mpr (show N₁≤A.card by omega)))
    have hm:=mul_le_mul_of_nonneg_left (hTlo i) (show 0≤p₀^2*η^2 by positivity)
    have hd:=mul_le_mul_of_nonneg_right hpp₂ (show 0≤η^2*(T i).card by positivity)
    nlinarith only [hh,hm,hd]
  apply hN V U Q F H n x A (by omega) hnθ hx hxA hSA hTlo hThi hbal hF hFx
  · intro i a ha'
    have he:ε≤p₀/2:=min_le_left _ _
    have hcoef:p₀/2≤p-ε:=by linarith only [he,hpp]
    have hh:=mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg (T i).card : (0:ℝ)≤(T i).card)
    nlinarith only [hh,hrow i a ha']
  · intro i u hu
    have hh:=mul_le_mul_of_nonneg_right hpp (Nat.cast_nonneg (T i).card : (0:ℝ)≤(T i).card)
    nlinarith only [hh,hcol i u hu]
  · intro i S hS J hJ hs hj
    have hb:0<(T i).card:=Nat.cast_pos.mp ((mul_pos hκ ha).trans_le (hTlo i))
    have hc:=degree_codegree_cuts_on_domains H F (Q.neighborFinset (x i)) (T i) p ε η d hp hp1 hε.le hη hb hF
      (fun a ha=>hrow i a ((Q.mem_neighborFinset (x i) a).mp ha))
      (fun a ha b hb=>hcodeg i a b ((Q.mem_neighborFinset (x i) a).mp ha) ((Q.mem_neighborFinset (x i) b).mp hb))
      hsmall (hmass i) S hS J hJ
      (by simpa only [η,div_div,show (4*16:ℝ)=64 by norm_num] using hs)
      (by simpa only [η,div_div,show (4*16:ℝ)=64 by norm_num] using hj)
    have hh:=mul_le_mul_of_nonneg_right hpp (show 0≤(S.card:ℝ)*J.card by positivity)
    nlinarith only [hc,hh]
  · exact hcount

end Oberwolfach
