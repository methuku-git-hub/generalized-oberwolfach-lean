module

public import Oberwolfach.ResidueDegreeDemands
public import Oberwolfach.SparseCorrectionMatrices

@[expose] public section

/-! Integer degree sequences for the fixed-type sparse correction.
All signed imbalances are retained, including the hub imbalance. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem integer_average_abs_le {I : Type*} [Fintype I]
    (hn : 0<Fintype.card I) (f : I → ℤ) {e : ℝ}
    (hf : ∀ i,|(f i : ℝ)|≤e) :
    |(∑ i,(f i : ℝ))/Fintype.card I|≤e := by
  exact abs_le.mpr (finite_average_interval hn (fun i=>(f i : ℝ)) (fun i=>abs_le.mp (hf i)))

theorem signed_total_natural_demands {I : Type*} [Fintype I]
    (hn : 0<Fintype.card I) (T : ℤ) (hT : 0≤T) :
    ∃ f : I → ℕ,(∑ i,(f i : ℤ))=T ∧
      ∀ i,|(f i : ℝ)-(T : ℝ)/Fintype.card I|≤1 := by
  obtain ⟨f,hf,hb⟩ := near_uniform_integer_demands hn T.toNat
  have ht : (T.toNat : ℤ)=T := Int.toNat_of_nonneg hT
  refine ⟨f,?_,?_⟩
  · exact (by exact_mod_cast hf : (∑ i,(f i : ℤ))=(T.toNat : ℤ)).trans ht
  · intro i
    have htR : (T.toNat : ℝ)=(T : ℝ) := by exact_mod_cast ht
    simpa only [htR] using hb i

theorem nat_demand_of_real_nonneg (a : ℤ) (ha : (0:ℝ)≤a) :
    (a.toNat : ℤ)=a := Int.toNat_of_nonneg (by exact_mod_cast ha)

/-- For the four deletion matrices, the two rim demand pairs have equal
integer totals and remove exactly the four supplied imbalances. -/
theorem typed_degree_demands {V U : Type*} [Fintype V] [Fintype U]
    (hn : 0<Fintype.card V) (hs : 0<Fintype.card U) (hsn : Fintype.card U≤Fintype.card V)
    (base q : ℕ) (hq : 1≤q) (bp bm bk : V → ℤ) (bw : U → ℤ)
    (htot : ∑ v,bp v=∑ v,bm v) {e : ℝ} (he : 0≤e)
    (hbp : ∀ v,|(bp v : ℝ)|≤e) (hbm : ∀ v,|(bm v : ℝ)|≤e)
    (hbk : ∀ v,|(bk v : ℝ)|≤e) (hbw : ∀ u,|(bw u : ℝ)|≤e)
    (hmargin : 3+4*e≤(Fintype.card U : ℝ)*base/Fintype.card V) :
    ∃ (a h ko ki ro ri : V → ℕ) (hu : U → ℕ),
      (∑ v,a v=Fintype.card U*base) ∧
      (∑ v,h v=∑ u,hu u) ∧ (∑ v,ko v=∑ v,ki v) ∧ (∑ v,ro v=∑ v,ri v) ∧
      (∀ v,(ko v : ℤ)+ro v-(a v+h v : ℕ)=bp v) ∧
      (∀ v,(ki v : ℤ)+ri v-(a v+h v : ℕ)=bm v) ∧
      (∀ v,(ki v : ℤ)-a v=bk v) ∧
      (∀ u,(hu u : ℤ)-q*base=bw u) ∧
      (∀ v,|(a v : ℝ)-(Fintype.card U : ℝ)*base/Fintype.card V|≤1) ∧
      (∀ v,|(h v : ℝ)-(∑ u,(hu u : ℝ))/Fintype.card V|≤1) ∧
      (∀ v,|(ko v : ℝ)-(∑ x,(ki x : ℝ))/Fintype.card V|≤1) ∧
      (∀ v,|(ki v : ℝ)-(∑ x,(ki x : ℝ))/Fintype.card V|≤1+2*e) ∧
      (∀ v,|(ro v : ℝ)-(∑ x,(ri x : ℝ))/Fintype.card V|≤3+2*e) ∧
      (∀ v,|(ri v : ℝ)-(∑ x,(ri x : ℝ))/Fintype.card V|≤1+4*e) := by
  classical
  let n : ℝ := Fintype.card V
  let s : ℝ := Fintype.card U
  let T : ℕ := Fintype.card U*base
  let μ : ℝ := s*base/n
  have hnR : 0<n := by dsimp [n];exact_mod_cast hn
  have hsR : 0<s := by dsimp [s];exact_mod_cast hs
  have hsnR : s≤n := by dsimp [s,n];exact_mod_cast hsn
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq
  have hμ : 3+4*e≤μ := hmargin
  have hμnon : 0≤μ := by positivity
  have hμbase : μ≤base := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsnR (Nat.cast_nonneg base : (0:ℝ)≤base)]
  have hbase : e≤base := by linarith
  obtain ⟨a,ha,haerr⟩ := near_uniform_integer_demands (V:=V) hn T
  have haR : (∑ v,(a v : ℝ))=s*base := by dsimp [s];exact_mod_cast ha
  have hae (v : V) : |(a v : ℝ)-μ|≤1 := by simpa only [T,Nat.cast_mul] using haerr v
  let hu (u : U) := ((q:ℤ)*base+bw u).toNat
  have hhuZ (u : U) : (hu u : ℤ)=(q:ℤ)*base+bw u := by
    apply nat_demand_of_real_nonneg
    push_cast
    have hb := (abs_le.mp (hbw u)).1
    nlinarith [mul_nonneg (show (0:ℝ)≤q-1 by linarith) (Nat.cast_nonneg base : (0:ℝ)≤base)]
  have hhuR (u : U) : (hu u : ℝ)=(q:ℝ)*base+bw u := by exact_mod_cast hhuZ u
  let H : ℕ := ∑ u,hu u
  obtain ⟨h,hh,hherr⟩ := near_uniform_integer_demands (V:=V) hn H
  let BK : ℝ := (∑ v,(bk v : ℝ))/n
  let BM : ℝ := (∑ v,(bm v : ℝ))/n
  let BW : ℝ := (∑ u,(bw u : ℝ))/n
  have hBK : |BK|≤e := integer_average_abs_le hn bk hbk
  have hBM : |BM|≤e := integer_average_abs_le hn bm hbm
  have hBW : |BW|≤e := by
    have hb := integer_average_abs_le hs bw hbw
    rw [abs_le] at hb ⊢
    have hblo := (le_div_iff₀ hsR).mp hb.1
    have hbhi := (div_le_iff₀ hsR).mp hb.2
    constructor
    · apply (le_div_iff₀ hnR).mpr
      have := mul_le_mul_of_nonneg_left hsnR he
      nlinarith
    · apply (div_le_iff₀ hnR).mpr
      have := mul_le_mul_of_nonneg_left hsnR he
      nlinarith
  have hHR : (H : ℝ)=s*((q:ℝ)*base)+(∑ u,(bw u : ℝ)) := by
    simp only [H,Nat.cast_sum,hhuR,Finset.sum_add_distrib,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul]
    rfl
  have hHmean : (H : ℝ)/n=q*μ+BW := by rw [hHR];dsimp [μ,BW];ring
  have hhe (v : V) : |(h v : ℝ)-(q*μ+BW)|≤1 := by rw [← hHmean];exact hherr v
  let ki (v : V) := ((a v:ℤ)+bk v).toNat
  have hkiZ (v : V) : (ki v : ℤ)=(a v : ℤ)+bk v := by
    apply nat_demand_of_real_nonneg
    push_cast
    have ha' := abs_le.mp (hae v)
    have hb' := abs_le.mp (hbk v)
    linarith [ha'.1,hb'.1]
  have hkiR (v : V) : (ki v : ℝ)=(a v : ℝ)+bk v := by exact_mod_cast hkiZ v
  let TK : ℕ := ∑ v,ki v
  obtain ⟨ko,hko,hkoerr⟩ := near_uniform_integer_demands (V:=V) hn TK
  have hTKmean : (TK : ℝ)/n=μ+BK := by
    simp only [TK,Nat.cast_sum,hkiR,Finset.sum_add_distrib,haR]
    dsimp [μ,BK]
    ring
  have hkoe (v : V) : |(ko v : ℝ)-(μ+BK)|≤1 := by rw [← hTKmean];exact hkoerr v
  let ri (v : V) := ((h v : ℤ)+bm v-bk v).toNat
  let ro (v : V) := ((h v : ℤ)+a v+bp v-ko v).toNat
  have hqμ : μ≤q*μ := by nlinarith [mul_nonneg (show (0:ℝ)≤q-1 by linarith) hμnon]
  have hriZ (v : V) : (ri v : ℤ)=(h v : ℤ)+bm v-bk v := by
    apply nat_demand_of_real_nonneg
    push_cast
    have h1 := abs_le.mp (hhe v)
    have h2 := abs_le.mp (hbm v)
    have h3 := abs_le.mp (hbk v)
    have h4 := abs_le.mp hBW
    linarith [h1.1,h2.1,h3.2,h4.1]
  have hroZ (v : V) : (ro v : ℤ)=(h v : ℤ)+a v+bp v-ko v := by
    apply nat_demand_of_real_nonneg
    push_cast
    have h1 := abs_le.mp (hhe v)
    have h2 := abs_le.mp (hae v)
    have h3 := abs_le.mp (hbp v)
    have h4 := abs_le.mp (hkoe v)
    have h5 := abs_le.mp hBW
    have h6 := abs_le.mp hBK
    linarith [h1.1,h2.1,h3.1,h4.2,h5.1,h6.2]
  have hriR (v : V) : (ri v : ℝ)=(h v : ℝ)+bm v-bk v := by exact_mod_cast hriZ v
  have hroR (v : V) : (ro v : ℝ)=(h v : ℝ)+a v+bp v-ko v := by exact_mod_cast hroZ v
  have hsumR : (∑ v,ro v)=(∑ v,ri v) := by
    have hkoZ : (∑ v,(ko v : ℤ))=∑ v,(ki v : ℤ) := by exact_mod_cast hko
    have hz : (∑ v,(ro v : ℤ))=(∑ v,(ri v : ℤ)) := by
      simp only [hroZ,hriZ,Finset.sum_sub_distrib,Finset.sum_add_distrib,htot]
      have hk : (∑ v,(ko v : ℤ))=(∑ v,(a v : ℤ))+(∑ v,bk v) := by
        rw [hkoZ];simp only [hkiZ,Finset.sum_add_distrib]
      omega
    exact_mod_cast hz
  have hT0mean : (∑ v,(ri v : ℝ))/n=q*μ+BW+BM-BK := by
    simp only [hriR,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    have hhR : (∑ v,(h v : ℝ))=H := by exact_mod_cast hh
    rw [hhR]
    calc
      _ = (H : ℝ)/n+(∑ v,(bm v : ℝ))/n-(∑ v,(bk v : ℝ))/n := by ring
      _ = _ := by rw [hHmean]
  refine ⟨a,h,ko,ki,ro,ri,hu,ha,hh,hko,hsumR,?_,?_,?_,?_,hae,(by simpa only [H,Nat.cast_sum] using hherr),(by simpa only [TK,Nat.cast_sum] using hkoerr),?_,?_,?_⟩
  · intro v; rw [hroZ];push_cast;ring
  · intro v; rw [hkiZ,hriZ];push_cast;ring
  · intro v;rw [hkiZ];ring
  · intro u;rw [hhuZ];ring
  · intro v
    rw [← Nat.cast_sum,← show TK=∑ x,ki x from rfl,hTKmean,hkiR,abs_le]
    have h1 := abs_le.mp (hae v)
    have h2 := abs_le.mp (hbk v)
    have h3 := abs_le.mp hBK
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]
  · intro v
    rw [hT0mean,hroR,abs_le]
    have h1 := abs_le.mp (hhe v)
    have h2 := abs_le.mp (hae v)
    have h3 := abs_le.mp (hbp v)
    have h4 := abs_le.mp (hkoe v)
    have h5 := abs_le.mp hBM
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]
  · intro v
    rw [hT0mean,hriR,abs_le]
    have h1 := abs_le.mp (hhe v)
    have h2 := abs_le.mp (hbm v)
    have h3 := abs_le.mp (hbk v)
    have h4 := abs_le.mp hBM
    have h5 := abs_le.mp hBK
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2]


/-- A centered bound implies the upper demand hypothesis of the proved
integral cut theorem; the common lower mean is kept explicit. -/
theorem near_uniform_matrix_degrees_centered {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (L : X → Y → ℕ) (f : X → ℕ) (g : Y → ℕ) {δ h E μ : ℝ}
    (hn : 0<Fintype.card X) (hs : 0<Fintype.card Y)
    (hδ : 0≤δ) (hδsmall : δ<1/4) (htot : ∑ x,f x=∑ y,g y)
    (hcap : (∑ x,(f x : ℝ))≤h*Fintype.card X*Fintype.card Y/2)
    (hμf : μ≤(∑ x,(f x : ℝ))/Fintype.card X)
    (hμg : μ≤(∑ y,(g y : ℝ))/Fintype.card Y)
    (hE : E≤δ*μ)
    (hf : ∀ x,|(f x : ℝ)-(∑ z,(f z : ℝ))/Fintype.card X|≤E)
    (hg : ∀ y,|(g y : ℝ)-(∑ z,(g z : ℝ))/Fintype.card Y|≤E)
    (hcut : BipartiteLargeCut L δ h) :
    ∃ J : X → Y → ℕ,(∀ x y,J x y≤L x y) ∧
      (∀ x,∑ y,J x y=f x) ∧ (∀ y,∑ x,J x y=g y) := by
  have ht : (∑ x,(f x : ℝ))=∑ y,(g y : ℝ) := by exact_mod_cast htot
  apply near_uniform_matrix_degrees L f g hn hs hδ hδsmall
    (Finset.sum_nonneg (fun x _=>Nat.cast_nonneg _)) hcap rfl ht.symm
  · intro x
    have hh := (abs_le.mp (hf x)).2
    have hm := mul_le_mul_of_nonneg_left hμf hδ
    calc
      _ ≤ (1+δ)*((∑ z,(f z : ℝ))/Fintype.card X) := by linarith
      _ = _ := by ring
  · intro y
    have hh := (abs_le.mp (hg y)).2
    have hm := mul_le_mul_of_nonneg_left hμg hδ
    rw [← ht] at hh hm
    calc
      _ ≤ (1+δ)*((∑ z,(f z : ℝ))/Fintype.card Y) := by linarith
      _ = _ := by ring
  · exact hcut

/-- Four actual integral deletion matrices. No graph factor or correction
operator is assumed: each matrix is obtained from the normalized cut theorem. -/
theorem typed_integer_correction_matrices {V U : Type*}
    [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (A₀ Aₖ : V → V → ℕ) (H₀ Hₖ : V → U → ℕ)
    (hn : 0<Fintype.card V) (hs : 0<Fintype.card U) (hsn : Fintype.card U≤Fintype.card V)
    (base q : ℕ) (hq : 1≤q) (bp bm bk : V → ℤ) (bw : U → ℤ)
    (htot : ∑ v,bp v=∑ v,bm v) {e δ hc : ℝ} (he : 0≤e)
    (hδ : 0≤δ) (hδsmall : δ<1/4)
    (hbp : ∀ v,|(bp v : ℝ)|≤e) (hbm : ∀ v,|(bm v : ℝ)|≤e)
    (hbk : ∀ v,|(bk v : ℝ)|≤e) (hbw : ∀ u,|(bw u : ℝ)|≤e)
    (hmargin : 3+4*e≤δ*((Fintype.card U : ℝ)*base/Fintype.card V-3*e))
    (hcap : (q:ℝ)*base+3*e≤hc*Fintype.card V/2)
    (hcut0 : BipartiteLargeCut A₀ δ hc) (hcutK : BipartiteLargeCut Aₖ δ hc)
    (hcutH0 : BipartiteLargeCut H₀ δ hc) (hcutHK : BipartiteLargeCut Hₖ δ hc) :
    ∃ (J₀ Jₖ : V → V → ℕ) (L₀ Lₖ : V → U → ℕ),
      (∀ x y,J₀ x y≤A₀ x y) ∧ (∀ x y,Jₖ x y≤Aₖ x y) ∧
      (∀ v u,L₀ v u≤H₀ v u) ∧ (∀ v u,Lₖ v u≤Hₖ v u) ∧
      (∀ v,(∑ x,(J₀ v x : ℤ))+(∑ x,(Jₖ v x : ℤ))-
        (∑ u,(L₀ v u : ℤ))-(∑ u,(Lₖ v u : ℤ))=bp v) ∧
      (∀ v,(∑ x,(J₀ x v : ℤ))+(∑ x,(Jₖ x v : ℤ))-
        (∑ u,(L₀ v u : ℤ))-(∑ u,(Lₖ v u : ℤ))=bm v) ∧
      (∀ v,(∑ x,(Jₖ x v : ℤ))-(∑ u,(Lₖ v u : ℤ))=bk v) ∧
      (∀ u,(∑ v,(L₀ v u : ℤ))-(q:ℤ)*(∑ v,(Lₖ v u : ℤ))=bw u) ∧
      (∀ v,(∑ x,(J₀ v x : ℝ))≤(q+2:ℝ)*base ∧
        (∑ x,(J₀ x v : ℝ))≤(q+2:ℝ)*base ∧
        (∑ x,(Jₖ v x : ℝ))≤(q+2:ℝ)*base ∧
        (∑ x,(Jₖ x v : ℝ))≤(q+2:ℝ)*base ∧
        (∑ u,(L₀ v u : ℝ))≤(q+2:ℝ)*base ∧
        (∑ u,(Lₖ v u : ℝ))≤(q+2:ℝ)*base) ∧
      (∀ u,(∑ v,(L₀ v u : ℝ))≤(q+2:ℝ)*base ∧
        (∑ v,(Lₖ v u : ℝ))≤(q+2:ℝ)*base) := by
  classical
  let n : ℝ := Fintype.card V
  let s : ℝ := Fintype.card U
  let μ : ℝ := s*base/n
  have hnR : 0<n := by dsimp [n];exact_mod_cast hn
  have hsR : 0<s := by dsimp [s];exact_mod_cast hs
  have hsnR : s≤n := by dsimp [s,n];exact_mod_cast hsn
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq
  have hμnon : 0≤μ := by positivity
  have hμbase : μ≤base := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hsnR (Nat.cast_nonneg base : (0:ℝ)≤base)]
  have hμpos : 0<μ-3*e := by
    by_contra hh
    have hp := mul_nonpos_of_nonneg_of_nonpos hδ (le_of_not_gt hh)
    linarith
  have hplain : 3+4*e≤μ := by nlinarith
  obtain ⟨a,h,ko,ki,ro,ri,hu,ha,hh,hko,hro,hop,hip,hik,hiu,hae,hhe,hkoe,hkie,hroe,hrie⟩ :=
    typed_degree_demands hn hs hsn base q hq bp bm bk bw htot he hbp hbm hbk hbw hplain
  let BK : ℝ := (∑ v,(bk v : ℝ))/n
  let BM : ℝ := (∑ v,(bm v : ℝ))/n
  let BW : ℝ := (∑ u,(bw u : ℝ))/n
  let BWu : ℝ := (∑ u,(bw u : ℝ))/s
  have hBK : |BK|≤e := integer_average_abs_le hn bk hbk
  have hBM : |BM|≤e := integer_average_abs_le hn bm hbm
  have hBWu : |BWu|≤e := integer_average_abs_le hs bw hbw
  have hBW : |BW|≤e := by
    rw [abs_le] at hBWu ⊢
    have hblo := (le_div_iff₀ hsR).mp hBWu.1
    have hbhi := (div_le_iff₀ hsR).mp hBWu.2
    constructor
    · apply (le_div_iff₀ hnR).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsnR he]
    · apply (div_le_iff₀ hnR).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsnR he]
  have haR : (∑ v,(a v : ℝ))=s*base := by dsimp [s];exact_mod_cast ha
  have hhR : (∑ v,(h v : ℝ))=∑ u,(hu u : ℝ) := by exact_mod_cast hh
  have hkoR : (∑ v,(ko v : ℝ))=∑ v,(ki v : ℝ) := by exact_mod_cast hko
  have hroR : (∑ v,(ro v : ℝ))=∑ v,(ri v : ℝ) := by exact_mod_cast hro
  have hhuR (u : U) : (hu u : ℝ)=(q:ℝ)*base+bw u := by
    have hh : (hu u : ℝ)-(q:ℝ)*base=bw u := by exact_mod_cast hiu u
    linarith
  have hkiR (v : V) : (ki v : ℝ)=(a v : ℝ)+bk v := by
    have hh : (ki v : ℝ)-a v=bk v := by exact_mod_cast hik v
    linarith
  have hriR (v : V) : (ri v : ℝ)=(h v : ℝ)+bm v-bk v := by
    have hh : (ki v : ℝ)+ri v-((a v : ℝ)+h v)=bm v := by exact_mod_cast hip v
    rw [hkiR] at hh
    linarith
  have hsumhu : (∑ u,(hu u : ℝ))=s*((q:ℝ)*base)+(∑ u,(bw u : ℝ)) := by
    simp only [hhuR,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rfl
  have hHmean : (∑ v,(h v : ℝ))/n=q*μ+BW := by rw [hhR,hsumhu];dsimp [μ,BW];ring
  have hHumean : (∑ u,(hu u : ℝ))/s=q*base+BWu := by
    rw [hsumhu]
    dsimp [BWu]
    field_simp
  have hKmean : (∑ v,(ki v : ℝ))/n=μ+BK := by
    simp only [hkiR,Finset.sum_add_distrib,haR]
    dsimp [μ,BK];ring
  have hRmean : (∑ v,(ri v : ℝ))/n=q*μ+BW+BM-BK := by
    simp only [hriR,Finset.sum_sub_distrib,Finset.sum_add_distrib]
    calc
      _ = (∑ v,(h v : ℝ))/n+(∑ v,(bm v : ℝ))/n-(∑ v,(bk v : ℝ))/n := by ring
      _ = _ := by rw [hHmean]
  have hqμ : μ≤q*μ := by nlinarith [mul_nonneg (show (0:ℝ)≤q-1 by linarith) hμnon]
  have hqbase : (base:ℝ)≤q*base := by nlinarith [mul_nonneg (show (0:ℝ)≤q-1 by linarith) (Nat.cast_nonneg base : (0:ℝ)≤base)]
  have hHlo : μ-3*e≤(∑ v,(h v : ℝ))/n := by rw [hHmean];linarith [(abs_le.mp hBW).1]
  have hHulo : μ-3*e≤(∑ u,(hu u : ℝ))/s := by rw [hHumean];linarith [(abs_le.mp hBWu).1]
  have hKlo : μ-3*e≤(∑ v,(ki v : ℝ))/n := by rw [hKmean];linarith [(abs_le.mp hBK).1]
  have hRlo : μ-3*e≤(∑ v,(ri v : ℝ))/n := by
    rw [hRmean];linarith [(abs_le.mp hBW).1,(abs_le.mp hBM).1,(abs_le.mp hBK).2]
  have hHcap : (∑ v,(h v : ℝ))≤hc*n*s/2 := by
    have hh' : (∑ u,(hu u : ℝ))/s≤hc*n/2 := by rw [hHumean];linarith [(abs_le.mp hBWu).2]
    rw [hhR]
    nlinarith [(div_le_iff₀ hsR).mp hh']
  have hKcap : (∑ v,(ko v : ℝ))≤hc*n*n/2 := by
    rw [hkoR]
    have hh' : (∑ v,(ki v : ℝ))/n≤hc*n/2 := by rw [hKmean];linarith [(abs_le.mp hBK).2]
    nlinarith [(div_le_iff₀ hnR).mp hh']
  have hRcap : (∑ v,(ro v : ℝ))≤hc*n*n/2 := by
    rw [hroR]
    have hm := mul_le_mul_of_nonneg_left hμbase (Nat.cast_nonneg q : (0:ℝ)≤q)
    have hh' : (∑ v,(ri v : ℝ))/n≤hc*n/2 := by
      rw [hRmean];linarith [(abs_le.mp hBW).2,(abs_le.mp hBM).2,(abs_le.mp hBK).1]
    nlinarith [(div_le_iff₀ hnR).mp hh']
  have hHKcap : (∑ v,(a v : ℝ))≤hc*n*s/2 := by
    rw [haR]
    have hb : (base:ℝ)≤hc*n/2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hb hsR.le]
  have hhuErr (u : U) : |(hu u : ℝ)-(∑ v,(hu v : ℝ))/s|≤3+4*e := by
    rw [hhuR,hHumean,abs_le]
    have h1 := abs_le.mp (hbw u)
    have h2 := abs_le.mp hBWu
    constructor <;> linarith [h1.1,h1.2,h2.1,h2.2]
  have hHKtot : ∑ v,a v=∑ _ : U,base := by simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul] using ha
  have hHKmean : (∑ _ : U,(base:ℝ))/s=base := by simp [s,ne_of_gt hsR]
  have hamean : (∑ v,(a v : ℝ))/n=μ := by rw [haR]
  obtain ⟨Lₖ,hLK,hLKrow,hLKcol⟩ := near_uniform_matrix_degrees_centered Hₖ a (fun _=>base)
    hn hs hδ hδsmall hHKtot hHKcap
    (show μ-3*e≤(∑ v,(a v : ℝ))/n by rw [hamean];linarith)
    (show μ-3*e≤(∑ _ : U,(base:ℝ))/s by rw [hHKmean];linarith)
    hmargin (fun v=>(by rw [hamean];exact (hae v).trans (by linarith)))
    (fun u=>by rw [hHKmean];simp only [sub_self,abs_zero];linarith) hcutHK
  obtain ⟨L₀,hL0,hL0row,hL0col⟩ := near_uniform_matrix_degrees_centered H₀ h hu
    hn hs hδ hδsmall hh hHcap hHlo hHulo hmargin
    (fun v=>by rw [hhR];exact (hhe v).trans (by linarith)) hhuErr hcutH0
  obtain ⟨Jₖ,hJK,hJKrow,hJKcol⟩ := near_uniform_matrix_degrees_centered Aₖ ko ki
    hn hn hδ hδsmall hko hKcap (by rw [hkoR];exact hKlo) hKlo hmargin
    (fun v=>by rw [hkoR];exact (hkoe v).trans (by linarith))
    (fun v=>(hkie v).trans (by linarith)) hcutK
  obtain ⟨J₀,hJ0,hJ0row,hJ0col⟩ := near_uniform_matrix_degrees_centered A₀ ro ri
    hn hn hδ hδsmall hro hRcap (by rw [hroR];exact hRlo) hRlo hmargin
    (fun v=>by rw [hroR];exact (hroe v).trans (by linarith))
    (fun v=>(hrie v).trans (by linarith)) hcut0
  have hbounds (v : V) : (a v : ℝ)≤(q+2:ℝ)*base ∧ (h v : ℝ)≤(q+2:ℝ)*base ∧
      (ko v : ℝ)≤(q+2:ℝ)*base ∧ (ki v : ℝ)≤(q+2:ℝ)*base ∧
      (ro v : ℝ)≤(q+2:ℝ)*base ∧ (ri v : ℝ)≤(q+2:ℝ)*base := by
    have h1 := (abs_le.mp (hae v)).2
    have h2 := (abs_le.mp (hhe v)).2
    have h3 := (abs_le.mp (hkoe v)).2
    have h4 := (abs_le.mp (hkie v)).2
    have h5 := (abs_le.mp (hroe v)).2
    have h6 := (abs_le.mp (hrie v)).2
    change (a v : ℝ)-μ≤1 at h1
    rw [← hhR,hHmean] at h2
    rw [hKmean] at h3 h4
    rw [hRmean] at h5 h6
    have h7 := (abs_le.mp hBW).2
    have h8 := abs_le.mp hBK
    have h9 := (abs_le.mp hBM).2
    have h10 := mul_le_mul_of_nonneg_left hμbase (Nat.cast_nonneg q : (0:ℝ)≤q)
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · nlinarith only [h1,hqbase,hμbase,hplain,he]
    · nlinarith only [h2,h10,h7,hplain,hμbase,he]
    · nlinarith only [h3,h8.2,hqbase,hplain,hμbase,he]
    · nlinarith only [h4,h8.2,hqbase,hplain,hμbase,he]
    · nlinarith only [h5,h10,h7,h9,h8.1,hplain,hμbase,he]
    · nlinarith only [h6,h10,h7,h9,h8.1,hplain,hμbase,he]
  have hhubbound (u : U) : (hu u : ℝ)≤(q+2:ℝ)*base := by
    rw [hhuR]
    nlinarith only [(abs_le.mp (hbw u)).2,hplain,hμbase,he]
  refine ⟨J₀,Jₖ,L₀,Lₖ,hJ0,hJK,hL0,hLK,?_,?_,?_,?_,?_,?_⟩
  · intro v
    have h1 : (∑ x,(J₀ v x : ℤ))=ro v := by exact_mod_cast hJ0row v
    have h2 : (∑ x,(Jₖ v x : ℤ))=ko v := by exact_mod_cast hJKrow v
    have h3 : (∑ u,(L₀ v u : ℤ))=h v := by exact_mod_cast hL0row v
    have h4 : (∑ u,(Lₖ v u : ℤ))=a v := by exact_mod_cast hLKrow v
    rw [h1,h2,h3,h4]
    have hh := hop v
    push_cast at hh
    linarith
  · intro v
    have h1 : (∑ x,(J₀ x v : ℤ))=ri v := by exact_mod_cast hJ0col v
    have h2 : (∑ x,(Jₖ x v : ℤ))=ki v := by exact_mod_cast hJKcol v
    have h3 : (∑ u,(L₀ v u : ℤ))=h v := by exact_mod_cast hL0row v
    have h4 : (∑ u,(Lₖ v u : ℤ))=a v := by exact_mod_cast hLKrow v
    rw [h1,h2,h3,h4]
    have hh := hip v
    push_cast at hh
    linarith
  · intro v
    have h1 : (∑ x,(Jₖ x v : ℤ))=ki v := by exact_mod_cast hJKcol v
    have h2 : (∑ u,(Lₖ v u : ℤ))=a v := by exact_mod_cast hLKrow v
    rw [h1,h2];exact hik v
  · intro u
    have h1 : (∑ v,(L₀ v u : ℤ))=hu u := by exact_mod_cast hL0col u
    have h2 : (∑ v,(Lₖ v u : ℤ))=base := by exact_mod_cast hLKcol u
    rw [h1,h2];exact hiu u
  · intro v
    have h1 : (∑ x,(J₀ v x : ℝ))=ro v := by exact_mod_cast hJ0row v
    have h2 : (∑ x,(J₀ x v : ℝ))=ri v := by exact_mod_cast hJ0col v
    have h3 : (∑ x,(Jₖ v x : ℝ))=ko v := by exact_mod_cast hJKrow v
    have h4 : (∑ x,(Jₖ x v : ℝ))=ki v := by exact_mod_cast hJKcol v
    have h5 : (∑ u,(L₀ v u : ℝ))=h v := by exact_mod_cast hL0row v
    have h6 : (∑ u,(Lₖ v u : ℝ))=a v := by exact_mod_cast hLKrow v
    rw [h1,h2,h3,h4,h5,h6]
    exact ⟨(hbounds v).2.2.2.2.1,(hbounds v).2.2.2.2.2,(hbounds v).2.2.1,
      (hbounds v).2.2.2.1,(hbounds v).2.1,(hbounds v).1⟩
  · intro u
    have h1 : (∑ v,(L₀ v u : ℝ))=hu u := by exact_mod_cast hL0col u
    have h2 : (∑ v,(Lₖ v u : ℝ))=base := by exact_mod_cast hLKcol u
    rw [h1,h2]
    exact ⟨hhubbound u,by nlinarith only [hqbase,(Nat.cast_nonneg base : (0:ℝ)≤base)]⟩

end Oberwolfach
