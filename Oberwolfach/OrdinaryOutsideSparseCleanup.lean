module

public import Oberwolfach.PrescribedEdgeEnumeration
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! Cover every sparse outside-outside rim edge and spoke by edge-disjoint
wheels, with all other vertices in the inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_sparse_outside_cleanup (Q F:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (r K D₀:ℕ) (hr:3≤r) (hK:0<K) (hQF:Disjoint Q F)
    (L bV bU:ℝ) (hL:0≤L) (hF:∀v,(F.degree v:ℝ)≤L)
    (hcount:∀u,∀a c,bV≤(((X.filter (fun w=>H w u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hubs:∀x∉X,∀y∉X,Q.Adj x y→bU≤((Z.filter (fun u=>H x u∧H y u)).card:ℝ)):
    let I:=(Finset.univ:Finset V)\X;
    let J:=(Finset.univ:Finset U)\Z;
    let E:=ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J);
    (∀t,(E.filter (ordinaryResourceIncident t)).card≤D₀)→
    (E.card*r:ℕ)/(K:ℝ)+(K*r:ℕ)+((r:ℝ)+2)*(L+1)+4*(K+D₀:ℕ)<bV→
    (E.card:ℝ)/K+2*(K+D₀:ℕ)<bU→
    (E.card*r:ℕ)/(K:ℝ)+(D₀*r:ℕ)+((r:ℝ)+2)*(L+1)+8*(K+D₀:ℕ)<bV→
    ∃(Nr Ns:ℕ) (C:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H r),
      (∀i j,i≠j→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim C) (wheelFamilySpokes C) r ∧
      (∀v∉X,∀w∉X,¬(Q\wheelFamilyRim C).Adj v w) ∧
      (∀v∉X,∀u∉Z,¬(H v u∧¬wheelFamilySpokes C v u)) ∧
      (∀w:V⊕U,((ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C)).degree w:ℝ)≤
        (max (6*(K+D₀)) ((K+D₀)*r):ℕ)):=by
  intro I J E hDE hbr hbu hbs
  have hIX:Disjoint I X:=Finset.sdiff_disjoint
  have hJZ:Disjoint J Z:=Finset.sdiff_disjoint
  have hFE:∀v w,Sum.inl s(v,w)∈E→¬F.Adj v w:=by
    intro v w hvw hf
    have hh:=(ordinaryHostResources_rim (spanningRestriction Q I) _ s(v,w)).mp hvw
    have hq:=((spanningRestriction_adj Q I v w).mp hh).1
    exact (disjoint_iff_inf_le.mp hQF) (v:=v) (w:=w) ⟨hq,hf⟩
  obtain ⟨Nr,Ns,x,y,z,u,hcard,hx,hy,hxy,hFxy,hedge,hend,hz,hu,hsp,hspinj,hsrow,hscol,heE⟩:=
    prescribed_inner_edge_enumeration Q F H I J E D₀ (fun _ h=>h) hFE hDE
  have hNr:Nr≤E.card:=by omega
  have hNs:Ns≤E.card:=by omega
  have hrR:((Nr*r:ℕ):ℝ)/(K:ℝ)≤((E.card*r:ℕ):ℝ)/(K:ℝ):=by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.mul_le_mul_right r hNr
  have hsR:((Ns*r:ℕ):ℝ)/(K:ℝ)≤((E.card*r:ℕ):ℝ)/(K:ℝ):=by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Nat.mul_le_mul_right r hNs
  have hrU:(Nr:ℝ)/(K:ℝ)≤(E.card:ℝ)/(K:ℝ):=
    div_le_div_of_nonneg_right (Nat.cast_le.mpr hNr) (Nat.cast_nonneg _)
  obtain ⟨C,hdis,hinner,hd,hs,hcol⟩:=prescribed_inner_edge_wheel_packing Q F H I X J Z hIX hJZ
    Nr Ns r K D₀ hr hK x y hx hy hxy hFxy hedge hend z u hz hu hsp hspinj hsrow hscol L bV bU hL hF
    (fun v _=>hcount v)
    (fun i=>hubs (x i) (by simpa [I] using hx i) (y i) (by simpa [I] using hy i) (hxy i))
    (by linarith only [hrR,hbr]) (by linarith only [hrU,hbu]) (by linarith only [hsR,hbs])
  have he:=prescribed_wheel_family_exact_union C E
    (Sum.elim (fun i=>Sum.inl s(x i,y i)) (fun i=>Sum.inr (z i,u i))) hdis hinner
  have hEcover:E⊆ordinaryHostResources (wheelFamilyRim C) (wheelFamilySpokes C):=by
    rw [←heE,←he.2.1]
    exact Finset.inter_subset_left
  refine ⟨Nr,Ns,C,hdis,he.1,?_,?_,?_⟩
  · intro v hv w hw h
    have hq:Q.Adj v w:=h.1
    have hvI:v∈I:=by simp [I,hv]
    have hwI:w∈I:=by simp [I,hw]
    have he':Sum.inl s(v,w)∈E:=(ordinaryHostResources_rim _ _ _).mpr
      ((spanningRestriction_adj Q I v w).mpr ⟨hq,hvI,hwI⟩)
    exact h.2 ((ordinaryHostResources_rim _ _ _).mp (hEcover he'))
  · intro v hv u hu h
    have hvI:v∈I:=by simp [I,hv]
    have huJ:u∈J:=by simp [J,hu]
    have he':Sum.inr (v,u)∈E:=(ordinaryHostResources_spoke _ _ _ _).mpr ⟨h.1,hvI,huJ⟩
    exact h.2 ((ordinaryHostResources_spoke _ _ _ _).mp (hEcover he'))
  · intro w
    cases w with
    | inl v=>
      rw [ordinary_physical_degree_row]
      have hs':(Finset.univ.filter (wheelFamilySpokes C v)).card≤2*(K+D₀):=by
        convert hs v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
      have hh:=Nat.add_le_add (hd v) hs'
      have hb:((wheelFamilyRim C).degree v+(Finset.univ.filter (wheelFamilySpokes C v)).card)≤6*(K+D₀):=by omega
      exact_mod_cast hb.trans (le_max_left _ _)
    | inr u=>
      rw [ordinary_physical_degree_column]
      exact_mod_cast (hcol u).trans (le_max_right _ _)
end Oberwolfach
