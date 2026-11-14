import FibrasDeHistorias
import Mathlib.Algebra.BigOperators.Fin
open scoped BigOperators
namespace ArticuloA.Revelado
noncomputable section
open Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

def tramo (p : α) (T : Finset α) (x : α) : Fin 3 := if x=p then 1 else if x∈T then 2 else 0
abbrev Fibra (f : α → Fin 3) (i : Fin 3) := {x // f x=i}
abbrev Respeta (f g : α → Fin 3) := {s : Equiv.Perm α // ∀ x,g (s x)=f x}

private def restringir {f g : α → Fin 3} (s : Respeta f g) (i : Fin 3) : Fibra f i ≃ Fibra g i :=
  s.val.subtypeEquiv (fun x => by rw [s.property])

private def bloques (f g : α → Fin 3) : Respeta f g ≃ (∀ i, Fibra f i ≃ Fibra g i) where
  toFun := restringir
  invFun e := ⟨Equiv.ofFiberEquiv e,Equiv.ofFiberEquiv_map e⟩
  left_inv s := by apply Subtype.ext; apply Equiv.ext; intro x; rfl
  right_inv e := by
    funext i; apply Equiv.ext; rintro ⟨x,hx⟩
    subst i
    apply Subtype.ext
    rfl

theorem medidas_bloques (p : α) (T : Finset α) (hp : p∉T) :
    Fintype.card (Fibra (tramo p T) 0) = Fintype.card α -1-T.card ∧
    Fintype.card (Fibra (tramo p T) 1) = 1 ∧
    Fintype.card (Fibra (tramo p T) 2) = T.card := by
  have ch (i : Fin 3) : Fintype.card (Fibra (tramo p T) i) =
      (Finset.univ.filter (fun x => tramo p T x=i)).card := Fintype.card_subtype _
  have a : Finset.univ.filter (fun x => tramo p T x=0) = (Finset.univ.erase p) \ T := by
    ext x; by_cases e : x=p <;> by_cases h : x∈T <;> simp [tramo,e,h,Finset.mem_sdiff]
  have b : Finset.univ.filter (fun x => tramo p T x=1) = {p} := by
    ext x; by_cases e : x=p <;> by_cases h : x∈T <;> simp [tramo,e,h]
  have c : Finset.univ.filter (fun x => tramo p T x=2) = T := by
    ext x; by_cases e : x=p <;> by_cases h : x∈T <;> simp_all [tramo]
  have sub : T ⊆ Finset.univ.erase p := by
    intro x hx; exact Finset.mem_erase.mpr ⟨fun e => hp (e ▸ hx),Finset.mem_univ _⟩
  simp [ch,a,b,c,Finset.card_sdiff sub,Finset.card_erase_of_mem (Finset.mem_univ p)]

theorem contar_ordenes (t p : α) (U T : Finset α) (ht : t∉U) (hp : p∉T) (sz : U.card=T.card) :
    Fintype.card (Respeta (tramo t U) (tramo p T)) =
    (Fintype.card α-1-T.card).factorial * T.card.factorial := by
  have A := medidas_bloques t U ht
  have B := medidas_bloques p T hp
  have eq (i : Fin 3) : Fintype.card (Fibra (tramo t U) i)=Fintype.card (Fibra (tramo p T) i) := by
    have h : i=0 ∨ i=1 ∨ i=2 := by omega
    rcases h with rfl|rfl|rfl <;> omega
  have count (i : Fin 3) : Fintype.card (Fibra (tramo t U) i ≃ Fibra (tramo p T) i) =
      (Fintype.card (Fibra (tramo p T) i)).factorial := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (eq i)),eq]
  rw [Fintype.card_congr (bloques _ _),Fintype.card_pi,Fin.prod_univ_three,count,count,count,B.1,B.2.1,B.2.2]
  simp

omit [Fintype α] in
theorem evento_exacto (t p : α) (U T : Finset α) (ht : t∉U) (hp : p∉T) (s : Equiv.Perm α) :
    (∀ x,tramo p T (s x)=tramo t U x) ↔ s t=p ∧ U.image s=T := by
  constructor
  · intro h
    have atP := h t
    have eq : s t=p := by
      by_contra ne
      by_cases hit : s t∈T <;> simp [tramo,ne,hit] at atP
    refine ⟨eq,?_⟩
    ext y; obtain ⟨x,rfl⟩ := s.surjective y
    have sim : s x∈U.image s ↔ x∈U := by simp [Finset.mem_image,s.injective.eq_iff]
    rw [sim]
    by_cases atT : x=t
    · subst x; simp [eq,ht,hp]
    · have ne : s x ≠ p := fun e => atT (s.injective (e.trans eq.symm))
      have hx := h x
      by_cases u : x∈U <;> by_cases v : s x∈T <;> simp_all [tramo]
  · rintro ⟨eq,im⟩ x
    by_cases e : x=t
    · subst x; simp [tramo,eq]
    · have ne : s x ≠ p := fun a => e (s.injective (a.trans eq.symm))
      have mem : s x∈T ↔ x∈U := by rw [←im]; simp [Finset.mem_image,s.injective.eq_iff]
      simp [tramo,e,ne,mem]

/-- In an order of N pieces t is a rank, p the chosen piece, and U the ranks after t.
Every possible set of later pieces of the same size has the same mass. -/
theorem masa_rango_y_conjunto {N : ℕ} (t p : Fin N) (T : Finset (Fin N)) (hp : p∉T)
    (sz : (Finset.univ.filter (fun r : Fin N => t<r)).card=T.card) :
    let U := Finset.univ.filter (fun r : Fin N => t<r)
    (Fintype.card {s : Equiv.Perm (Fin N) // s t=p ∧ U.image s=T}:ℝ) / N.factorial =
      ((N-1-T.card).factorial:ℝ) * (T.card.factorial:ℝ) / N.factorial := by
  intro U
  have ht : t ∉ U := by simp [U]
  have bij := Equiv.subtypeEquivRight (fun s : Equiv.Perm (Fin N) => (evento_exacto t p U T ht hp s).symm)
  rw [Fintype.card_congr bij]
  change (Fintype.card (Respeta (tramo t U) (tramo p T)):ℝ) / _ = _
  have aux := contar_ordenes t p U T ht hp sz
  simp only [Fintype.card_fin] at aux
  apply congrArg (fun z : ℝ => z / (N.factorial:ℝ))
  rw [← Nat.cast_mul]
  apply congrArg (fun k : ℕ => (k:ℝ))
  convert aux using 1
  congr 1
  exact Subsingleton.elim _ _
omit [Fintype α] in
theorem supervivencia_en_un_rango (U S : Finset α) (hs : S ⊆ U) (m : ℕ) (hm : m≤U.card) :
    (((U.powersetCard m).filter (fun T => S ⊆ T)).card:ℝ) / ((U.powersetCard m).card:ℝ) =
      (m.choose S.card:ℝ)/(U.card.choose S.card:ℝ) := by
  by_cases small : S.card≤m
  · have bij : ((U.powersetCard m).filter (fun T => S⊆T)).card =
        ((U \ S).powersetCard (m-S.card)).card := by
      apply Finset.card_bij' (fun T _ => T \ S) (fun D _ => D ∪ S)
      · intro T h
        obtain ⟨ht,hsub⟩ := Finset.mem_filter.mp h
        obtain ⟨tu,size⟩ := Finset.mem_powersetCard.mp ht
        exact Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset_sdiff tu (Finset.Subset.refl _),
          (Finset.card_sdiff hsub).trans (by rw [size])⟩
      · intro D h
        obtain ⟨sub,size⟩ := Finset.mem_powersetCard.mp h
        have dis : Disjoint D S := Finset.disjoint_left.mpr (fun _ hd => (Finset.mem_sdiff.mp (sub hd)).2)
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.union_subset (sub.trans Finset.sdiff_subset) hs,?_⟩,Finset.subset_union_right⟩
        rw [Finset.card_union_of_disjoint dis,size]; omega
      · intro T h
        exact Finset.sdiff_union_of_subset (Finset.mem_filter.mp h).2
      · intro D h
        have sub := (Finset.mem_powersetCard.mp h).1
        ext x; by_cases hd : x∈D <;> by_cases ss : x∈S <;> simp_all [Finset.mem_sdiff]
        exact (Finset.mem_sdiff.mp (sub hd)).2 ss
    rw [bij,Finset.card_powersetCard,Finset.card_powersetCard,Finset.card_sdiff hs]
    apply (div_eq_div_iff (by exact_mod_cast (Nat.choose_pos hm).ne')
      (by exact_mod_cast (Nat.choose_pos (Finset.card_le_card hs)).ne')).mpr
    have eq := Nat.choose_mul hm small
    exact_mod_cast (by simpa only [mul_comm] using eq.symm : (U.card-S.card).choose (m-S.card) * U.card.choose S.card = m.choose S.card * U.card.choose m)
  · have empty : ((U.powersetCard m).filter (fun T => S⊆T))=∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro T h
      obtain ⟨ht,st⟩ := Finset.mem_filter.mp h
      have size := (Finset.mem_powersetCard.mp ht).2
      exact small (size ▸ Finset.card_le_card st)
    simp [empty,Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge small)]
private theorem potencia_descendente (m u s : ℕ) (hm : m≤u) :
    m.descFactorial s*u^s ≤ u.descFactorial s*m^s := by
  induction s with
  | zero => simp
  | succ j ih =>
    rw [Nat.descFactorial_succ,Nat.descFactorial_succ,pow_succ,pow_succ]
    have one : (m-j)*u ≤ (u-j)*m := by
      by_cases lim : j≤m
      · have l := congrArg (fun a : ℕ => a*u) (Nat.sub_add_cancel lim)
        have r := congrArg (fun a : ℕ => a*m) (Nat.sub_add_cancel (lim.trans hm))
        dsimp only at l r
        nlinarith [Nat.mul_le_mul_left j hm]
      · simp [Nat.sub_eq_zero_of_le (by omega : m≤j)]
    calc
      _ = ((m-j)*u)*(m.descFactorial j*u^j) := by ring
      _ ≤ ((u-j)*m)*(u.descFactorial j*m^j) := Nat.mul_le_mul one ih
      _ = _ := by ring

theorem cota_hipergeometrica (m u s : ℕ) (hm : m≤u) (hs : s≤u) (pos : 0<u) :
    (m.choose s:ℝ)/(u.choose s:ℝ) ≤ ((m:ℝ)/u)^s := by
  have cross := potencia_descendente m u s hm
  simp only [Nat.descFactorial_eq_factorial_mul_choose,mul_assoc] at cross
  have small : m.choose s*u^s ≤ u.choose s*m^s := Nat.le_of_mul_le_mul_left cross (Nat.factorial_pos _)
  rw [div_pow]
  apply (div_le_div_iff₀ (by exact_mod_cast Nat.choose_pos hs) (pow_pos (by exact_mod_cast pos) s)).mpr
  exact_mod_cast (by simpa only [mul_comm] using small : m.choose s*u^s ≤ m^s*u.choose s)
end
end ArticuloA.Revelado
#print axioms ArticuloA.Revelado.masa_rango_y_conjunto
#print axioms ArticuloA.Revelado.supervivencia_en_un_rango
#print axioms ArticuloA.Revelado.cota_hipergeometrica
