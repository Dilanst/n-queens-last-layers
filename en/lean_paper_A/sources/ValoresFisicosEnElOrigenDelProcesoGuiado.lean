import IdentificacionDelObservableDeLineaAntesDeLaParada
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem peso_fisico_en_tiempo_cero {n} (v : Cell n→ℝ≥0) (q : ℕ) (e : Cell n) (s : Finset (Fin 4)) :
    pesoDeFamiliasG v q 0 e s=(v e:ℝ) := by simp [pesoDeFamiliasG,fraccionVivaG]

theorem masa_global_inicial {n} (v : Cell n→ℝ≥0) (q : ℕ) (f : Cell n→ℝ) :
    pesoObservable (fun e=>pesoDeFamiliasG v q 0 e Finset.univ*f e) (some [])=∑ e,(v e:ℝ)*f e := by
  simp [pesoObservable,masaVivaEn,peso_fisico_en_tiempo_cero]

theorem W_inicia_con_la_masa_de_entrada {n} (v : Cell n→ℝ≥0) (q : ℕ) :
    (total masas (opcionesGuiadas v q 0 [])).val=∑ e,(v e:ℝ) := by
  rw [normalizador_real_del_paso_G]
  simp [pesoObservable,masaVivaEn,pesoGuiado]

theorem Z_inicia_en_la_masa_de_su_linea {n} (v : Cell n→ℝ≥0) (q : ℕ) (i : Fin 4) (z : Cell n) :
    masaObservadaDeLinea v q 0 [] i z=(masaDeLineaG v i z:ℝ) := by
  unfold masaObservadaDeLinea masaDeLineaG
  simp only [fraccionVivaG,Nat.cast_zero,zero_div,zero_mul,sub_zero,one_mul]
  simp only [masaVivaEn,List.not_mem_nil,false_implies,implies_true,if_true,pesoGuiado,
    Nat.cast_zero,zero_div,zero_mul,tsub_zero,Finset.prod_const_one,div_one]
  rw [fibraFisicaG,Finset.sum_filter,NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : llaveDeLinea i e=llaveDeLinea i z <;> simp [h]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.W_inicia_con_la_masa_de_entrada
#print axioms ArticuloA.Historias.Z_inicia_en_la_masa_de_su_linea
