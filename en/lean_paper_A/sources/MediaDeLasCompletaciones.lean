import NormalizadorDeLaPiezaMarcada
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel E2 RealFinita Revelado
noncomputable section
open Classical
variable {n q : ℕ}

theorem multiplicidad_real (P : Tablero n q) (C : Completion P) :
    (Finset.univ.filter (fun p : Indice n => esReal (pieza P C p)=true)).card=q := by
  let E := Finset.univ.filter (fun p : Indice n => esReal (pieza P C p)=true)
  have eq : E.image Fin.val=ocupados P 0 := by
    ext x; constructor
    · intro hx; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      have hr := (Finset.mem_filter.mp hp).2
      unfold pieza at hr
      split at hr
      · rename_i h
        exact h.choose_spec.2 ▸ en_ocupados P h.choose h.choose_spec.1 0
      · contradiction
    · intro hx
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      refine Finset.mem_image.mpr ⟨⟨lines e 0,rango e 0⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
      rw [encuentra P C e he]; rfl
  have nd : ((queens P.val).map (fun e => lines e 0)).Nodup :=
    List.pairwise_map.mpr ((legal_y_tamano P).1.imp (fun r => (separadas _ _).mp r 0))
  have s := congrArg Finset.card eq
  simpa only [E,Finset.card_image_of_injective _ Fin.val_injective,ocupados,
    List.toFinset_card_of_nodup nd,List.length_map,queenLength,(legal_y_tamano P).2] using s

theorem suma_colores (P : Tablero n q) (C : Completion P) (u : ColorWeights ℝ≥0) :
    ∑ p : Indice n,logColor n u (pieza P C p)=
      q*Real.log (Wreal n u)+(↑(2*n-1-q):ℝ)*Real.log (Wvirtual n u) := by
  let b := fun p : Indice n => esReal (pieza P C p)=true
  have r : (Finset.univ.filter b).card=q := multiplicidad_real P C
  have v : (Finset.univ.filter (fun p => ¬b p)).card=2*n-1-q := by
    have both := Finset.filter_card_add_filter_neg_card_eq_card (s:=Finset.univ) b
    rw [r,Finset.card_univ,Fintype.card_fin] at both; omega
  unfold logColor
  change (∑ p : Indice n, if b p then _ else _) = _
  rw [Finset.sum_ite]
  simp only [Finset.sum_const,r,v,nsmul_eq_mul]

def costeLog (H : Historia n q) (h : ℕ) (u : ColorWeights ℝ≥0) :=
  ∑ t,Real.log ((denominador (estado H h t.val) u (secuencia H t)).val)

def cotaMedia (n q : ℕ) (hn : 2≤n) (u : ColorWeights ℝ≥0) (A : ℝ) :=
  q*Real.log (Wreal n u)+(↑(2*n-1-q):ℝ)*Real.log (Wvirtual n u)-4*(↑(2*n-1):ℝ)+restoRango n hn A

theorem media_en_completacion (P : Tablero n q) (C : Completion P) (h : ℕ) (hn : 2≤n)
    (u : ColorWeights ℝ≥0) (A : ℝ) (dif : Difusos n u A)
    (pos : ∀ p,0<(elegido u (pieza P C p)).val) :
    (∑ s : Equiv.Perm (Indice n),costeLog (⟨P,C,s⟩ : Historia n q) h u)/(2*n-1).factorial ≤
      cotaMedia n q hn u A := by
  let N : ℝ := (2*n-1:ℕ)
  have np : N≠0 := by dsimp [N]; exact_mod_cast (by omega : 2*n-1≠0)
  have bound := aplicar_rangos_al_nucleo P C h u _ (fun p => cota_de_pieza P C p hn u A dif (pos p))
  apply bound.trans_eq
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,suma_colores]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change (N*(_+_)-N*(4*N)+N*restoRango n hn A)/N=(_+_)-4*N+_
  field_simp; ring

theorem media_en_historias (h : ℕ) (hn : 2≤n) (level : 0<count n q)
    (u : ColorWeights ℝ≥0) (A : ℝ) (dif : Difusos n u A)
    (pos : ∀ (P : Tablero n q) (C : Completion P) p,0<(elegido u (pieza P C p)).val) :
    (∑ H : Historia n q,proba n q * costeLog H h u) ≤ cotaMedia n q hn u A := by
  let v := cotaMedia n q hn u A
  have sz (P : Tablero n q) (C : Completion P) :
      (∑ s : Equiv.Perm (Indice n),costeLog (⟨P,C,s⟩ : Historia n q) h u)≤
        ∑ _ : Equiv.Perm (Indice n),v := by
    have hh := (div_le_iff₀ (show (0:ℝ)<(2*n-1).factorial by positivity)).mp
      (media_en_completacion P C h hn u A dif (pos P C))
    simpa only [v,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul,
      mul_comm (cotaMedia n q hn u A)] using hh
  have total : (∑ H : Historia n q,costeLog H h u)≤∑ _ : Historia n q,v := by
    rw [Fintype.sum_sigma,Fintype.sum_sigma]
    apply Finset.sum_le_sum; intro P _
    conv_lhs => rw [Fintype.sum_prod_type]
    conv_rhs => rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum (fun C _ => sz P C)
  have card : (Fintype.card (Historia n q):ℝ)≠0 := by
    rw [card_historias,Nat.cast_mul,multiplicidad,Nat.cast_mul,Nat.cast_pow]; positivity
  rw [←Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left total (by unfold proba; positivity : 0≤proba n q)).trans_eq
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,proba,←mul_assoc,inv_mul_cancel₀ card,one_mul]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.media_en_completacion
#print axioms ArticuloA.Historias.media_en_historias
