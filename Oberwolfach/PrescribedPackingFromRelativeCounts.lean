module

public import Oberwolfach.PrescribedRelativeExtensionCounts
public import Oberwolfach.PrescribedEdgePacking
public import Oberwolfach.PrescribedEdgeParameters

@[expose] public section

/-! Prescribed inner edges are covered from the actual relative counts.
The cap and all deletion margins are chosen here; no wheel-extension
existence assumption is supplied by the caller. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_inner_packing_from_relative_counts (r:ℕ) (hr:3≤r) (p₀ γ ω:ℝ)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (hγ:0<γ) (hγ1:γ≤1) (hω:0<ω):
    ∃ α₀:ℝ,0<α₀ ∧ α₀≤1 ∧ ∀ α L:ℝ,0<α → α≤α₀ → 0≤L → ∃ m₀:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (P Q F:SimpleGraph V) (H:V→U→Prop)
    (A I X:Finset V) (U₀ J B:Finset U) (hIX:Disjoint I X) (hJB:Disjoint J B)
    (Nr Ns D₀:ℕ)
    (x y:Fin Nr→V) (hx:∀ i,x i∈I) (hy:∀ i,y i∈I)
    (hxy:∀ i,Q.Adj (x i) (y i)) (hFxy:∀ i,¬F.Adj (x i) (y i))
    (hedge:∀ i j,i≠j → ¬((x i=x j∧y i=y j)∨(x i=y j∧y i=x j)))
    (hend:∀ a,(Finset.univ.filter (fun i=>a=x i∨a=y i)).card≤D₀)
    (z:Fin Ns→V) (u:Fin Ns→U) (hz:∀ i,z i∈I) (hu:∀ i,u i∈J) (hH:∀ i,H (z i) (u i))
    (hspoke:Function.Injective (fun i=>(z i,u i)))
    (hsend:∀ a,(Finset.univ.filter (fun i=>a=z i)).card≤D₀)
    (hshub:∀ v,(Finset.univ.filter (fun i=>u i=v)).card≤D₀)
    (hJB0:J∪B⊆U₀) (hm:m₀≤A.card)
    (hN:((Nr+Ns:ℕ):ℝ)≤α^2*(A.card:ℝ)^2) (hD:(D₀:ℝ)≤α*A.card)
    (hωU:ω*A.card≤(U₀.card:ℝ)) (hF:∀ a,(F.degree a:ℝ)≤L)
    (q p ε:ℝ) (hq:p₀≤q) (hp:p₀≤p) (hε:ε≤p₀^6*γ/4)
    (hdeg:∀ v,(1/2+γ)*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hXA:((A\X).card:ℝ)≤p₀^6*γ*A.card/8)
    (hBU:((U₀\B).card:ℝ)≤p₀^6*γ*U₀.card/8)
    (hrow:∀ S:Finset V,∀ J':Finset U,J'⊆U₀ → S.card≤2 → J'.card≤1 →
      |((common (common A S (fun v=>Q.neighborFinset v)) J'
        (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
        q^S.card*p^J'.card*(common A S (fun v=>P.neighborFinset v)).card|≤ε*A.card)
    (hindex:∀ S:Finset V,S.card≤2 → (∀ v∈S,∀ w∈S,¬F.Adj v w) →
      |((common U₀ S (fun v=>Finset.univ.filter (H v))).card:ℝ)-p^S.card*U₀.card|≤ε*U₀.card),
    ∃ C:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H r,
      (∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      (∀ i,ordinaryWheelResources (C i)∩ordinaryHostResources (spanningRestriction Q I)
        (fun a v=>H a v∧a∈I∧v∈J)=
        {Sum.elim (fun j=>Sum.inl s(x j,y j)) (fun j=>Sum.inr (z j,u j)) i}) ∧
      (∀ a,((wheelFamilyRim C).degree a:ℝ)≤12*α*A.card) ∧
      (∀ a,((Finset.univ.filter (fun v=>wheelFamilySpokes C a v)).card:ℝ)≤6*α*A.card) ∧
      (∀ v,((Finset.univ.filter (fun a=>wheelFamilySpokes C a v)).card:ℝ)≤3*α*A.card*r) :=by
  let b:ℝ:=p₀^6*γ/8*min 1 ω
  have hb:0<b:=by dsimp [b];positivity
  obtain ⟨α₀,hα₀,hα₀1,hparams⟩:=prescribed_edge_cap_parameters r b hb
  refine ⟨α₀,hα₀,hα₀1,?_⟩
  intro α L hα hαsmall hL
  obtain ⟨m₀,hm₀⟩:=hparams α L hα hαsmall hL
  refine ⟨m₀,?_⟩
  intro V U _ _ _ _ P Q F H A I X U₀ J B hIX hJB Nr Ns D₀ x y hx hy hxy hFxy hedge hend
    z u hz hu hH hspoke hsend hshub hJB0 hm hN hD hωU hF q p ε hq hp hε hdeg hXA hBU hrow hindex
  let K:=⌈α*A.card⌉₊
  obtain ⟨hK,hKhi,hbR,hbU,hbS⟩:=hm₀ A.card (Nr+Ns) D₀ hm hN hD
  have hext:=prescribed_relative_extension_counts P Q F H A X U₀ B p₀ q p γ ε
    hp₀ hp₀1 hq hp hγ hγ1 hε hdeg hXA hBU hrow hindex
  have hbA:b*A.card≤(p₀^6*γ/8)*A.card:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) ω) (show 0≤p₀^6*γ/8 by positivity)
    have hh':=mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg A.card)
    dsimp [b];nlinarith only [hh']
  have hbU0:b*A.card≤(p₀^6*γ/8)*U₀.card:=by
    have hh:=mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) ω) (Nat.cast_nonneg A.card)
    have hh':=mul_le_mul_of_nonneg_left (hh.trans hωU) (show 0≤p₀^6*γ/8 by positivity)
    dsimp [b];nlinarith only [hh']
  have hK0:(0:ℝ)≤K:=Nat.cast_nonneg _
  have hRfrac:((Nr*r:ℕ):ℝ)/K≤(((Nr+Ns)*r:ℕ):ℝ)/K:=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.mul_le_mul_right r (Nat.le_add_right _ _))) hK0
  have hRfrac':(Nr:ℝ)/K≤((Nr+Ns:ℕ):ℝ)/K:=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.le_add_right _ _)) hK0
  have hSfrac:((Ns*r:ℕ):ℝ)/K≤(((Nr+Ns)*r:ℕ):ℝ)/K:=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.mul_le_mul_right r (Nat.le_add_left _ _))) hK0
  obtain ⟨C,hC,hinner,hCr,hCs,hCc⟩:=prescribed_inner_edge_wheel_packing Q F H I X J B hIX hJB
    Nr Ns r K D₀ hr hK x y hx hy hxy hFxy hedge hend z u hz hu hH hspoke hsend hshub L (b*A.card) (b*A.card) hL hF
    (fun v hv a c=>hbA.trans (hext.1 v (hJB0 hv) a c))
    (fun i=>hbU0.trans (hext.2 (x i) (y i) (hFxy i)))
    (by linarith only [hbR,hRfrac]) (by linarith only [hbU,hRfrac']) (by linarith only [hbS,hSfrac])
  have hKD:((K+D₀:ℕ):ℝ)≤3*α*A.card:=by
    simp only [Nat.cast_add]
    linarith only [hKhi,hD]
  refine ⟨C,hC,hinner,?_,?_,?_⟩
  · intro a
    have hh:((wheelFamilyRim C).degree a:ℝ)≤4*(K+D₀:ℕ):=by exact_mod_cast hCr a
    linarith only [hh,hKD]
  · intro a
    have hh:((Finset.univ.filter (fun v=>wheelFamilySpokes C a v)).card:ℝ)≤2*(K+D₀:ℕ):=by exact_mod_cast hCs a
    linarith only [hh,hKD]
  · intro v
    have hh:((Finset.univ.filter (fun a=>wheelFamilySpokes C a v)).card:ℝ)≤(K+D₀:ℕ)*r:=by exact_mod_cast hCc v
    have hs:=mul_le_mul_of_nonneg_right hKD (Nat.cast_nonneg r)
    nlinarith only [hh,hs]

end Oberwolfach
