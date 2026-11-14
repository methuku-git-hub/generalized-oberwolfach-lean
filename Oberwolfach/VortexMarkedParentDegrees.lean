module

public import Oberwolfach.VortexProtectedGeometry

@[expose] public section

/-! Actual parent and difference domains of a paired vortex satisfy the
near-regularity and minimum-degree hypotheses. Roots are retained on the
two-level external domain prescribed by the vortex definition. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem vortex_degree_margins (n D a u deg β α ρ : ℝ)
    (hn : 0< n) (ha : 0≤a) (hD : (1/2+α)*n≤D) (hDu : D≤n)
    (hα : 0<α) (hβ : 0≤β) (hβα : β≤α/8) (hβ1 : β≤1/4)
    (hc : |2*u/ρ-(D/n)*a|≤β*a) (hd : |deg-2*u/ρ|≤β*a) :
    a/2≤2*u/ρ ∧ 2*u/ρ≤2*a ∧ (1/2+α/2)*a≤deg := by
  have hDlo : 1/2+α≤D/n := (le_div_iff₀ hn).mpr hD
  have hDhi : D/n≤1 := (div_le_iff₀ hn).mpr (by simpa using hDu)
  have hlo := mul_le_mul_of_nonneg_right hDlo ha
  have hhi := mul_le_mul_of_nonneg_right hDhi ha
  have hbα := mul_le_mul_of_nonneg_right hβα ha
  have hb1 := mul_le_mul_of_nonneg_right hβ1 ha
  have hcp := (abs_le.mp hc).1
  have hcm := (abs_le.mp hc).2
  have hdp := (abs_le.mp hd).1
  constructor
  · nlinarith only [hlo,hcp,hbα,mul_nonneg hα.le ha]
  constructor
  · nlinarith only [hhi,hcm,hb1,ha]
  · nlinarith only [hlo,hcp,hdp,hbα,mul_nonneg hα.le ha]

theorem Vortex.marked_parent_degrees
    {V U : Type*} [Fintype V] [Fintype U] {G : SimpleGraph V}
    {D m : ℕ} {β ε α : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0< Fintype.card V)
    (hD : (1/2+α)*Fintype.card V≤(D:ℝ)) (hα : 0<α)
    (hρ : 0< initialIndexDensity U D) (hb : 0≤β) (hbα : β≤α/8) (hb1 : β≤1/4)
    {i : ℕ} (hi : i≤Q.length) (x : V) (hx : x∈Q.vertices (i-2)) :
    (Q.vertices i).card/2≤2*(Q.indices i).card/initialIndexDensity U D ∧
    2*(Q.indices i).card/initialIndexDensity U D≤2*(Q.vertices i).card ∧
    (1/2+α/2)*(Q.vertices i).card≤((G.neighborFinset x∩Q.vertices i).card:ℝ) ∧
    |((G.neighborFinset x∩Q.vertices i).card:ℝ)-2*(Q.indices i).card/initialIndexDensity U D|≤β*(Q.vertices i).card := by
  have he := Q.estimates_including_zero hreg hn hρ hb i hi
  have hn' : (0:ℝ)< Fintype.card V := by exact_mod_cast hn
  have hDu : (D:ℝ)≤Fintype.card V := by exact_mod_cast regular_degree_le_card hreg hn
  obtain ⟨ha,hb',hc⟩ := vortex_degree_margins (Fintype.card V) D (Q.vertices i).card (Q.indices i).card
    (G.neighborFinset x∩Q.vertices i).card β α (initialIndexDensity U D) hn' (Nat.cast_nonneg _)
    hD hDu hα hb hbα hb1 he.1 (he.2 x hx)
  exact ⟨ha,hb',hc,he.2 x hx⟩

theorem Vortex.marked_difference_parent_degrees
    {V U : Type*} [Fintype V] [Fintype U] {G : SimpleGraph V}
    {D m : ℕ} {β ε α : ℝ} (Q : Vortex U G D β ε m)
    (hreg : G.IsRegularOfDegree D) (hn : 0< Fintype.card V)
    (hD : (1/2+α)*Fintype.card V≤(D:ℝ)) (hα : 0<α)
    (hρ : 0< initialIndexDensity U D) (hb : 0≤β) (hbα : β≤3*α/40) (hb1 : β≤3/20)
    (he : 0≤ε) (he1 : ε≤1/4) {j k : ℕ} (hjk : j< k)
    (x : V) (hx : x∈Q.extendedVertices (k-2)) :
    let A:=Q.extendedVertices j\Q.extendedVertices k
    let B:=Q.extendedIndices j\Q.extendedIndices k;
    A.card/2≤2*B.card/initialIndexDensity U D ∧
    2*B.card/initialIndexDensity U D≤2*A.card ∧
    (1/2+α/2)*A.card≤((G.neighborFinset x∩A).card:ℝ) ∧
    |((G.neighborFinset x∩A).card:ℝ)-2*B.card/initialIndexDensity U D|≤(5/3)*β*A.card := by
  intro A B
  have hest := Q.extended_difference_degree_estimates hreg hn hρ hb he he1 hjk x hx
  have hn' : (0:ℝ)< Fintype.card V := by exact_mod_cast hn
  have hDu : (D:ℝ)≤Fintype.card V := by exact_mod_cast regular_degree_le_card hreg hn
  obtain ⟨ha,hb',hc⟩ := vortex_degree_margins (Fintype.card V) D A.card B.card
    (G.neighborFinset x∩A).card ((5/3)*β) α (initialIndexDensity U D) hn' (Nat.cast_nonneg _)
    hD hDu hα (by positivity) (by linarith only [hbα]) (by linarith only [hb1]) hest.1 hest.2
  exact ⟨ha,hb',hc,hest.2⟩

theorem Vortex.cover_down_parent_orders
    {V U : Type*} [Fintype V] [Fintype U] {G : SimpleGraph V}
    {D m : ℕ} {β ε : ℝ} (Q : Vortex U G D β ε m)
    (he : 0<ε) (hm : 0< m) {i : ℕ} (hi : i< Q.length) :
    (m:ℝ)/2≤(Q.vertices i).card := by
  have hl := Q.vertices_lower (by omega : i+1≤Q.length)
  have hu := (Q.consecutive_size_bounds he hm hi).2
  nlinarith only [hl,hu,he]

end Oberwolfach
