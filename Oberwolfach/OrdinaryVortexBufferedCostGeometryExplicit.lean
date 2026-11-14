module

public import Oberwolfach.FiniteWindowRecentCost
public import Oberwolfach.OrdinaryTraceCapacityScaleConstraint
public import Oberwolfach.MarkedFixedVortexEventInputs

@[expose] public section
/-! A fixed-length buffer has a uniformly bounded total recent cost on
    both inner sides, using the original vortex size estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_buffered_cost_from_geometry_explicit
    (ε ρ₀ δ:ℝ) (buffer:ℕ) (hbuffer:2≤buffer)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hδ:0<δ):
    ∃rate:ℝ,0<rate ∧ rate≤δ*(ε/2)^buffer ∧ ∀β:ℝ,0≤β→β≤1/4→∀C:ℝ,0≤C→∃m₀:ℕ,1≤m₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (i:ℕ),i+1<Q.length→∀cost:ℕ→ℝ,
      (∀j∈Finset.Icc (i+2-buffer) i,0≤cost j ∧
        cost j≤4*rate*Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)+C)→
    let loss:=∑j∈Finset.Icc (i+2-buffer) i,cost j;
    0≤loss ∧ loss≤δ*(markedVortexInnerVertices Q (i+1)).card ∧
      loss≤δ*(markedVortexInnerHubs Q (i+1)).card :=by
  let K:ℝ:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))
  have hK:1≤K:=by
    dsimp [K]
    have h1:0≤1/(ε/2):=by positivity
    have h2:0≤1/((ε/2)*(ρ₀/8)):=by positivity
    linarith
  let rate:ℝ:=δ/(32*((buffer:ℝ)+1)*K^buffer)
  have hrate:0<rate:=by dsimp [rate];positivity
  have hrateBound:(buffer:ℝ)*8*rate*K^buffer≤δ/4:=by
    have hb:(0:ℝ)≤buffer:=by positivity
    have heq:rate*(32*((buffer:ℝ)+1)*K^buffer)=δ:=by
      dsimp [rate]
      field_simp
    nlinarith [mul_nonneg hrate.le (show 0≤K^buffer by positivity)]
  have hKlower:2/ε≤K:=by
    have h1:1/(ε/2)=2/ε:=by field_simp
    dsimp [K]
    have h2:0≤1/((ε/2)*(ρ₀/8)):=by positivity
    linarith only [h1,h2]
  have hrateDecay:rate≤δ*(ε/2)^buffer:=ordinary_trace_rate_decay δ ε K rate buffer hδ.le hε hKlower le_rfl
  refine ⟨rate,hrate,hrateDecay,?_⟩
  intro β hβ hβ1 C hC
  obtain ⟨M,hM⟩:=exists_nat_gt (4*(buffer:ℝ)*C/δ)
  obtain ⟨m₀,hm₀,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q i hi cost hcost loss
  let a:ℕ→ℝ:=fun j=>Fintype.card (markedVortexVertexType Q j)
  let J:=Finset.Icc (i+2-buffer) i
  have hmpos:0<m:=by omega
  have hstep:∀j < i,a j≤K*a (j+1):=by
    intro j hj
    have h:=hsize V U P D m hreg hn hD hρlo hρhi hm Q j (by omega)
    have heq:((markedVortexInnerVertices Q j).card:ℝ)=a (j+1):=by
      rw [(marked_vortex_inner_cardinalities Q j).1]
      simp [a,markedVortexVertexType]
    simpa only [K,heq] using h.2.2.2.1
  have hlocal:∀j∈J,cost j≤(8*rate)*a j+C:=by
    intro j hj
    have hjle:j ≤ i:=(Finset.mem_Icc.mp hj).2
    have hu:Fintype.card (markedVortexHubType Q j)≤Fintype.card (markedVortexVertexType Q j):=
      (marked_vortex_fixed_ambient_size_fields Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε hmpos j (by omega)).2.2
    have huR:(Fintype.card (markedVortexHubType Q j):ℝ)≤a j:=by
      dsimp [a]
      exact_mod_cast hu
    have hp:Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)≤2*a j:=by
      simp only [Fintype.card_sum,Nat.cast_add,a]
      linarith
    have hh:4*rate*(Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j):ℝ)≤(8*rate)*a j:=by
      nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0≤4*rate)]
    exact (hcost j hj).2.trans (by linarith)
  have hsum:=finite_recent_window_cost_bound a cost K (8*rate) C i buffer hbuffer hK (by positivity) hC
    (by positivity) hstep hlocal
  have h1:=hsize V U P D m hreg hn hD hρlo hρhi hm Q i (by omega)
  have h2:=hsize V U P D m hreg hn hD hρlo hρhi hm Q (i+1) hi
  let I:ℝ:=(markedVortexInnerVertices Q (i+1)).card
  let B:ℝ:=(markedVortexInnerHubs Q (i+1)).card
  have hI0:0≤I:=by positivity
  have hB0:0≤B:=by positivity
  have hnext:((markedVortexInnerVertices Q i).card:ℝ)=a (i+1):=by
    rw [(marked_vortex_inner_cardinalities Q i).1]
    simp [a,markedVortexVertexType]
  have hprev:a i≤K*a (i+1):=by simpa only [K,hnext] using h1.2.2.2.1
  have hI:a (i+1)≤K*I:=by simpa only [K,a,I] using h2.2.2.2.1
  have hB:a (i+1)≤K*B:=by simpa only [K,a,B] using h2.2.2.2.2.2
  have hIscale:a i≤K^2*I:=by nlinarith [mul_le_mul_of_nonneg_left hI (by linarith : 0≤K)]
  have hBscale:a i≤K^2*B:=by nlinarith [mul_le_mul_of_nonneg_left hB (by linarith : 0≤K)]
  have hpow:K^(buffer-2)*K^2=K^buffer:=by rw [←pow_add];congr 1;omega
  have hbig:(4*(buffer:ℝ)*C/δ:ℝ)≤M:=hM.le
  have hMI:(M:ℝ)≤I:=by
    have hh:=h2.2.1
    change (M:ℝ)≤(1-ε)*I at hh
    nlinarith [mul_nonneg hε.le hI0]
  have hMB:(M:ℝ)≤B:=by
    have hh:=h2.2.2.1
    change (M:ℝ)≤(1-ε)*B at hh
    nlinarith [mul_nonneg hε.le hB0]
  have hCI:(buffer:ℝ)*C≤δ*I/4:=by
    have hh:4*(buffer:ℝ)*C≤δ*(M:ℝ):=by
      have h:= (div_le_iff₀ hδ).mp hbig
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hMI hδ.le]
  have hCB:(buffer:ℝ)*C≤δ*B/4:=by
    have hh:4*(buffer:ℝ)*C≤δ*(M:ℝ):=by
      have h:= (div_le_iff₀ hδ).mp hbig
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hMB hδ.le]
  have hsum0:0≤loss:=by
    dsimp [loss]
    exact Finset.sum_nonneg (fun j hj=>(hcost j hj).1)
  refine ⟨hsum0,?_,?_⟩
  · have hmult:=mul_le_mul_of_nonneg_left hIscale (show 0≤(buffer:ℝ)*(8*rate)*K^(buffer-2) by positivity)
    have hmult':(buffer:ℝ)*(8*rate)*K^(buffer-2)*a i≤(buffer:ℝ)*8*rate*K^buffer*I:=by
      calc
        _ ≤ (buffer:ℝ)*(8*rate)*K^(buffer-2)*(K^2*I):=hmult
        _ = (buffer:ℝ)*8*rate*K^buffer*I:=by rw [←hpow];ring
    have hbudget:=mul_le_mul_of_nonneg_right hrateBound hI0
    change loss≤δ*I
    dsimp [loss] at hsum ⊢
    nlinarith only [hsum,hmult',hbudget,hCI,mul_nonneg hδ.le hI0]
  · have hmult:=mul_le_mul_of_nonneg_left hBscale (show 0≤(buffer:ℝ)*(8*rate)*K^(buffer-2) by positivity)
    have hmult':(buffer:ℝ)*(8*rate)*K^(buffer-2)*a i≤(buffer:ℝ)*8*rate*K^buffer*B:=by
      calc
        _ ≤ (buffer:ℝ)*(8*rate)*K^(buffer-2)*(K^2*B):=hmult
        _ = (buffer:ℝ)*8*rate*K^buffer*B:=by rw [←hpow];ring
    have hbudget:=mul_le_mul_of_nonneg_right hrateBound hB0
    change loss≤δ*B
    dsimp [loss] at hsum ⊢
    nlinarith only [hsum,hmult',hbudget,hCB,mul_nonneg hδ.le hB0]
end Oberwolfach
