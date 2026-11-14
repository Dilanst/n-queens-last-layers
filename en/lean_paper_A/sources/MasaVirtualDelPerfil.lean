import LogaritmosDelPerfil
open MeasureTheory Set
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2
noncomputable section
private theorem muestra_transversal (n : ℕ) (hn : 0<n) (v : ℝ→ℝ≥0) (κ L : ℝ) (lp : 0≤L)
    (reg : RegularEn unidadCerrada v κ L) (mass : (∫ x in (0:ℝ)..1,(v x:ℝ))=1) :
    familiaReal n (fun y => v y)-(n:ℝ)≤L := by
  have e:=cuadratura_centros n hn (fun y => (v y:ℝ)) L lp (continua_de_cota lp reg.oscilacion) reg.oscilacion
  rw [mass,mul_one,abs_sub_comm] at e
  simpa only [familiaReal,centro,nodo,medio,zero_add] using (abs_le.mp e).2

private theorem muestra_oblicua (n : ℕ) (hn : 0<n) (h : ℕ) (a : ℝ) (v : ℝ→ℝ≥0) (κ L : ℝ) (lp : 0≤L)
    (reg : RegularEn (Icc a (a+2)) v κ L) (edge : v a=1)
    (mass : (n:ℝ)*(∫ x in a..(a+2),(v x:ℝ))=n+h) :
    familiaOblicua n a (fun y => v y)-((n:ℝ)+h-1)≤2*L+2 := by
  have e:=cuadratura_diagonales n hn a (fun y => (v y:ℝ)) L lp (continua_de_cota lp reg.oscilacion) reg.oscilacion
  rw [mass,abs_sub_comm] at e
  dsimp only at e
  rw [edge,NNReal.coe_one,abs_one] at e
  have ue := (abs_le.mp e).2
  simp only [Perfil.interior,nodo,oblicuo,Nat.cast_add,Nat.cast_one,add_zero] at ue
  unfold familiaOblicua oblicuo; linarith

theorem cotas_cuatro_sumas (n h : ℕ) (hn : 2≤n) (x : ℝ≥0) (x1 : (x:ℝ)≤1) (cuota : (x:ℝ)*(n:ℝ)=(h:ℝ))
    (p : FactoresContinuos) (κ L : ℝ) (lp : 0≤L)
    (r : RegularEn unidadCerrada p.fila κ L) (c : RegularEn unidadCerrada p.columna κ L)
    (d : RegularEn (Icc (-1) 1) p.diagonal κ L) (a : RegularEn (Icc 0 2) p.anti κ L)
    (dr : p.diagonal (-1)=1) (ar : p.anti 0=1)
    (rm : (∫ y in (0:ℝ)..1,(p.fila y:ℝ))=1) (cm : (∫ y in (0:ℝ)..1,(p.columna y:ℝ))=1)
    (dm : (n:ℝ)*(∫ y in (-1:ℝ)..1,(p.diagonal y:ℝ))=n+h)
    (am : (n:ℝ)*(∫ y in (0:ℝ)..2,(p.anti y:ℝ))=n+h) :
    ∀ j : Fin 4,sumasVirtuales n (sameColors (pesosMalla n x p)) j-((n:ℝ)+h-1)≤2*L+2 := by
  have np : 0<n := by omega
  have cast : (↑(n-1):ℝ)=n-1 := by rw [Nat.cast_sub (by omega : 1≤n),Nat.cast_one]
  obtain ⟨R,C,D,A⟩ := sumas_comunes n (by omega) x p
  have linear (S : ℝ) (bound : S-(n:ℝ)≤L) : (x:ℝ)*S+(↑(n-1):ℝ)-(n+h-1)≤2*L+2 := by
    rw [cast]
    have xb := mul_le_mul_of_nonneg_left bound x.property
    rw [mul_sub] at xb
    change (x:ℝ)*S-(x:ℝ)*(n:ℝ)≤(x:ℝ)*L at xb
    rw [cuota] at xb
    linarith [mul_le_mul_of_nonneg_right x1 lp]
  intro j; fin_cases j
  · change sumasVirtuales n _ (0 : Fin 4) - _ ≤ _
    rw [R]; exact linear _ (muestra_transversal n np _ _ _ lp r rm)
  · change sumasVirtuales n _ (1 : Fin 4) - _ ≤ _
    rw [C]; exact linear _ (muestra_transversal n np _ _ _ lp c cm)
  · change sumasVirtuales n _ (2 : Fin 4) - _ ≤ _
    rw [D]; exact muestra_oblicua n np h (-1) _ _ _ lp (by norm_num; exact d) dr (by norm_num; exact dm)
  · change sumasVirtuales n _ (3 : Fin 4) - _ ≤ _
    rw [A]; exact muestra_oblicua n np h 0 _ _ _ lp (by simpa using a) ar (by simpa using am)

theorem log_Wvirtual_desde_sumas (n h : ℕ) (hn : 2≤n) (nh : h≤n) (u : ColorWeights ℝ≥0)
    (E : ℝ) (positive : 0<Wvirtual n u)
    (est : ∀ j,sumasVirtuales n u j-((n:ℝ)+h-1)≤E) :
    (↑(2*n-1-(n-h)):ℝ)*(Real.log (Wvirtual n u)-4*Real.log (2*n-1-(n-h):ℕ))≤4*E := by
  have hid : 2*n-1-(n-h)=n-1+h := by omega
  have cast : (↑(2*n-1-(n-h)):ℝ)=n+h-1 := by rw [hid,Nat.cast_add,Nat.cast_sub (by omega : 1≤n),Nat.cast_one]; ring
  have hp : 0<(↑(2*n-1-(n-h)):ℝ) := by exact_mod_cast (by omega : 0<2*n-1-(n-h))
  have eq : Wvirtual n u = ∏ j,sumasVirtuales n u j := cuatro_sumas_virtuales n u
  rw [eq] at positive ⊢
  have pos (j : Fin 4) : 0<sumasVirtuales n u j := by
    have non : 0≤sumasVirtuales n u j := Finset.sum_nonneg (fun i _ => NNReal.coe_nonneg _)
    exact lt_of_le_of_ne non (fun z => positive.ne' (Finset.prod_eq_zero (Finset.mem_univ j) z.symm))
  exact error_de_masa_virtual _ _ hp _ pos (fun j => by rw [cast]; exact est j)

theorem virtual_lleno_equivale_a_x_cero (n : ℕ) (hn : 2≤n) (p : FactoresContinuos) (i : Fin 4) :
    sumasVirtuales n (coloresLlenos n (pesosMalla n 1 p)) i=sumasVirtuales n (sameColors (pesosMalla n 0 p)) i := by
  obtain ⟨r,c,d,a⟩ := sumas_llenas n (by omega) p
  obtain ⟨R,C,D,A⟩ := sumas_comunes n (by omega) 0 p
  fin_cases i <;> simp [r,c,d,a,R,C,D,A]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cotas_cuatro_sumas
#print axioms ArticuloA.Historias.log_Wvirtual_desde_sumas
#print axioms ArticuloA.Historias.virtual_lleno_equivale_a_x_cero
