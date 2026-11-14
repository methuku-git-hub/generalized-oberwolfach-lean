module

public import Oberwolfach.RootWheelCapParameters
public import Oberwolfach.OrdinaryLocalExtensions

@[expose] public section

/-! The internal-use cap is fixed before the conflict radius and graph
order. Source local-extension hypotheses produce all wheels at one root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_capped_root_wheels_from_local_extensions (r:ℕ) (hr:4≤r)
    (α ρ₀ s₀ C₀:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hρ₀1:ρ₀≤1) (hs₀:0<s₀) (hs₀1:s₀≤1) (hC₀:0≤C₀) :
    ∃ K:ℕ,0<K ∧ ∃ ε₀:ℝ,0<ε₀ ∧ ∀ d:ℕ,∃ n₀:ℕ,
      ∀ (V U:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U],
      ∀ (P R:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V)
        (A:Finset V) (B:Finset U) (ρ s ε:ℝ),n₀≤A.card →
      ρ₀≤ρ → s₀≤s → ε≤ε₀ →
      (∀ a,(cycleThreshold r+α)*A.card≤((A∩P.neighborFinset a).card:ℝ)) →
      (∀ X:Finset V,∀ J:Finset U,X.card≤ordinaryExtensionRootBound r → J.card≤2 →
        (ρ*s)^X.card*s^J.card*((common A X (fun a=>(P\permutationConflictGraph π (3*d)).neighborFinset a)).card:ℝ)-ε*A.card≤
          ((common (common A X (fun a=>R.neighborFinset a)) J
            (fun u=>Finset.univ.filter (fun a=>H a u))).card:ℝ)) →
      (∀ X:Finset V,X.card≤r+6 →
        (∀ a∈X,∀ b∈X,¬(permutationConflictGraph π (3*d)).Adj a b) →
        (s^X.card-ε)*B.card≤((common B X (fun a=>Finset.univ.filter (H a))).card:ℝ)) →
      ∀ N:ℕ,(N:ℝ)≤C₀*A.card → ∀ x:V,x∉A →
      ∀ (v w:Fin N→V) (u:Fin N→U),Function.Injective u →
      (∀ i,v i≠w i) → (∀ i j,i≠j → Disjoint ({v i,w i}:Finset V) {v j,w j}) →
      (∀ i,R.Adj x (v i)) → (∀ i,R.Adj x (w i)) →
      (∀ i,∀ a∈({x,v i,w i}:Finset V),∀ b∈({x,v i,w i}:Finset V),
        ¬(permutationConflictGraph π (3*d)).Adj a b) →
      (∀ i,H x (u i)∧H (v i) (u i)∧H (w i) (u i)) →
      ∃ W:Fin N→OrdinaryWheel R (permutationConflictGraph π (3*d)) H r,
        (∀ i,ordinaryWheelHub (W i)=u i ∧ (ordinaryWheelRim (W i)).Adj x (v i) ∧
          (ordinaryWheelRim (W i)).Adj x (w i) ∧
          (∀ a∈(ordinaryWheelRim (W i)).support,a∈({x,v i,w i}:Finset V) ∨ a∈A)) ∧
        (∀ i j,i≠j → Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j))) ∧
        (∀ a,rootWheelInternalLoad W x v w a≤K) ∧
        (∀ a,a≠x → (wheelFamilyRim W).degree a≤2*(K+1)) ∧
        (∀ a,(wheelFamilyRim W).Adj x a ↔ ∃ i,a=v i∨a=w i) ∧
        (∀ b,wheelFamilySpokes W x b ↔ ∃ i,u i=b) ∧
        (∀ a,a≠x → (Finset.univ.filter (fun b=>wheelFamilySpokes W a b)).card≤K+1) ∧
        (∀ b,(Finset.univ.filter (fun a=>wheelFamilySpokes W a b)).card≤r) := by
  obtain ⟨β,ε₀,hβ,hε,hN⟩:=ordinary_local_extensions r (by omega) α ρ₀ s₀ hα hρ₀ hρ₀1 hs₀ hs₀1
  obtain ⟨K,hK,ζ,hζ,N₀,hmargin⟩:=root_wheel_cap_parameters r C₀ β hC₀ hβ
  refine ⟨K,hK,ε₀,hε,?_⟩
  intro d
  obtain ⟨N₁,hN₁⟩:=hN d
  obtain ⟨N₂,hN₂⟩:=exists_nat_gt ((6*d:ℝ)/ζ)
  refine ⟨max N₀ (max N₁ N₂),?_⟩
  intro V U _ _ _ _ P R H π A B ρ s ε hn hρ hs hε' hdeg hrows hindices N hNcount x hxA v w u hu hvw hpair hxv hxw hFroot hHroot
  have hL: (6*d:ℝ)≤ζ*A.card:=by
    have hh:(6*d:ℝ)/ζ<(A.card:ℝ):=hN₂.trans_le (Nat.cast_le.mpr (by omega))
    have hh':=(div_lt_iff₀ hζ).mp hh
    nlinarith only [hh']
  have hext:=((hN₁ V U P R H π A B ρ s ε (by omega) hρ hs hε' hdeg hrows hindices).1)
  let T:Fin N→Finset V:=fun i=>A∩Finset.univ.filter (fun a=>H a (u i))
  have hcount (i:Fin N) (a b:V):β*A.card≤((T i∩R.neighborFinset a∩R.neighborFinset b).card:ℝ):=by
    have hh:=hext {a,b} {u i} (Finset.card_le_two.trans (by unfold ordinaryExtensionRootBound;split_ifs <;> omega)) (by simp)
    have he:common (common A {a,b} (fun v=>R.neighborFinset v)) {u i}
        (fun u=>Finset.univ.filter (fun v=>H v u))=T i∩R.neighborFinset a∩R.neighborFinset b:=by
      ext z
      simp only [common,Finset.mem_filter,Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton,
        forall_eq_or_imp,forall_eq,Finset.mem_univ,true_and,T]
      tauto
    rw [he] at hh
    exact hh
  have hF (a:V):((permutationConflictGraph π (3*d)).degree a:ℝ)≤6*d:=by
    have hh:=permutationConflictGraph_degree_le π (3*d) a
    exact_mod_cast (show (permutationConflictGraph π (3*d)).degree a≤6*d by omega)
  obtain ⟨W,hW,hdis,hcap,hdegree,hroot,hspoke,hrow,hcol⟩:=capped_ordinary_root_wheels R
    (permutationConflictGraph π (3*d)) H r N K hr hK x v w u hu hvw hpair T
    (fun i hx=>hxA (Finset.mem_inter.mp hx).1) hxv hxw hFroot hHroot
    (fun i a ha=>(Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2)
    (6*d) (β*A.card) (by positivity) hF (fun i a _ b _=>hcount i a b)
    (hmargin A.card N (by omega) hNcount (6*d) (by positivity) hL)
  refine ⟨W,?_,hdis,hcap,hdegree,hroot,hspoke,hrow,hcol⟩
  intro i
  refine ⟨(hW i).1,(hW i).2.1,(hW i).2.2.1,?_⟩
  intro a ha
  exact ((hW i).2.2.2 a ha).imp_right (fun h=>(Finset.mem_inter.mp h).1)

end Oberwolfach
