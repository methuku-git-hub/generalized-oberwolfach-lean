module

public import Oberwolfach.OrdinaryVortexCoverdownCostMargins
public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! Bound the actual root-first cover-down cost relative to both inner
sets two levels later, using only the fixed vortex geometry and uniform
smallness of the cover, cleanup and pairing rates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_root_cover_cost_from_geometry
    (ε ρ₀ δ:ℝ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hδ:0<δ):
    ∃rate:ℝ,0<rate ∧ ∀β:ℝ,0≤β→β≤1/4→∀C:ℝ,0≤C→∃m₀:ℕ,1≤m₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (i:ℕ),i+1<Q.length→∀(ν η ρ:ℝ),
      let parent:ℝ:=Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i);
      0≤ν→ν≤rate*parent→0≤η→η≤rate*parent→0≤ρ→ρ≤rate→
      let loss:=ν+η+(2*(ρ*parent)+C);
      0≤loss ∧ loss≤δ*(markedVortexInnerVertices Q (i+1)).card ∧
        loss≤δ*(markedVortexInnerHubs Q (i+1)).card:=by
  let K₀:ℝ:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))
  let K:ℝ:=2*(K₀+1)^2
  have hK₀:1≤K₀:=by
    dsimp [K₀]
    have h1:0≤1/(ε/2):=by positivity
    have h2:0≤1/((ε/2)*(ρ₀/8)):=by positivity
    linarith
  have hK:1≤K:=by dsimp [K];nlinarith [sq_nonneg K₀]
  obtain ⟨rate,hrate,hcost⟩:=ordinary_vortex_coverdown_cost_margins K δ hK hδ
  refine ⟨rate,hrate,?_⟩
  intro β hβ hβ1 C hC
  obtain ⟨M,hcost⟩:=hcost C hC
  obtain ⟨m₀,hm₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q i hi ν η ρ parent
    hν0 hν hη0 hη hρ0 hρ loss
  have h0:=hsize V U P D m hreg hn hD hρlo hρhi hm Q i (by omega)
  have h1:=hsize V U P D m hreg hn hD hρlo hρhi hm Q (i+1) hi
  let A:ℝ:=(markedVortexInnerVertices Q (i+1)).card
  let B:ℝ:=(markedVortexInnerHubs Q (i+1)).card
  let V0:ℝ:=Fintype.card (markedVortexVertexType Q i)
  let U0:ℝ:=Fintype.card (markedVortexHubType Q i)
  let V1:ℝ:=Fintype.card (markedVortexVertexType Q (i+1))
  have hA0:0≤A:=by positivity
  have hB0:0≤B:=by positivity
  have hV10:0≤V1:=by positivity
  have hsame:((markedVortexInnerVertices Q i).card:ℝ)=V1:=by
    rw [(marked_vortex_inner_cardinalities Q i).1]
    simp [V1,markedVortexVertexType]
  have hA:(M:ℝ)≤A:=by
    have he:0≤ε*A:=mul_nonneg hε.le hA0
    have h:=h1.2.1
    change (M:ℝ)≤(1-ε)*A at h
    nlinarith only [h,he]
  have hB:(M:ℝ)≤B:=by
    have he:0≤ε*B:=mul_nonneg hε.le hB0
    have h:=h1.2.2.1
    change (M:ℝ)≤(1-ε)*B at h
    nlinarith only [h,he]
  have hparent:parent=V0+U0:=by simp [parent,V0,U0]
  have hprev:parent≤2*K₀*V1:=by
    have hv:V0≤K₀*V1:=by simpa only [←hsame] using h0.2.2.2.1
    have hu:U0≤K₀*V1:=by simpa only [←hsame] using h0.2.2.2.2.1
    rw [hparent]
    linarith
  have hnextA:V1≤K₀*A:=h1.2.2.2.1
  have hnextB:V1≤K₀*B:=h1.2.2.2.2.2
  have hscale:2*K₀*K₀≤K:=by dsimp [K];nlinarith [sq_nonneg K₀]
  have hpA:parent≤K*A:=by
    have hmul:=mul_le_mul_of_nonneg_left hnextA (show 0≤2*K₀ by linarith)
    have hkA:=mul_le_mul_of_nonneg_right hscale hA0
    nlinarith only [hprev,hmul,hkA]
  have hpB:parent≤K*B:=by
    have hmul:=mul_le_mul_of_nonneg_left hnextB (show 0≤2*K₀ by linarith)
    have hkB:=mul_le_mul_of_nonneg_right hscale hB0
    nlinarith only [hprev,hmul,hkB]
  have hp0:0≤parent:=by positivity
  exact hcost A B parent ν η ρ hA hB hp0 hpA hpB hν0 hν hη0 hη hρ0 hρ
end Oberwolfach
