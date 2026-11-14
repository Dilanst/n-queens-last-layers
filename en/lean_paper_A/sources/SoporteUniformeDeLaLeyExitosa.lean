import TresCotasDelPerfilFisico
import UnaCotaParaTodasLasCapas
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.ProfileKernel Trayectoria.E2 RealFinita Revelado
noncomputable section
open Classical

private theorem soporte_desde_historias {n q h} (P : Tablero n q) (u : ColorWeights ℝ≥0)
    (level : q=n-h) (pos : ∀ H : Historia n q,0<(pesoCamino H h u).val)
    (den : ∀ (H : Historia n q) i,denominador (estado H h i.val) u (secuencia H i)≠0) :
    0<masaTablero P h u := by
  have card : 0<Fintype.card (Decoracion P) := by rw [card_fibra,multiplicidad]; positivity
  letI : Nonempty (Decoracion P) := Fintype.card_pos_iff.mp card
  have ok:=suma_en_la_fibra P h level u (fun H => pesoCamino H h u) (fun _ => camino_completo _ h level u (den _))
  exact (Finset.sum_pos (fun t _ => pos ⟨P,t⟩) Finset.univ_nonempty).trans_le ok

theorem masa_positiva_en_cada_tablero {n h} (hn : 0<n) (p : FactoresContinuos) {κ m L : ℝ}
    (sp : ControlEspacial p κ m L) (kp : 0<κ) (P : Tablero n (n-h)) :
    0<masaTablero P h (coloresDelPerfil n h p) := by
  by_cases hh : h=0
  · subst h; simp only [Nat.sub_zero] at P
    rw [coloresDelPerfil,if_pos rfl]
    let u:=pesosMalla n 1 p
    have hu:=factores_positivos hn sp kp 1 zero_lt_one
    apply soporte_desde_historias P (coloresLlenos n u) (by omega)
    · intro H
      rw [peso_fisico_en_lleno H u]
      have eq : ramaCero H (factores u)=masaRamaCon H (efectivos (factores u)) (fun J => normalizadorCero J (factores u)) := by
        dsimp only [ramaCero,masaRamaCon]; simp_rw [peso_sobre_el_soporte]
      rw [eq]; exact masaRamaCon_pos _ (fun J t => normalizadorCero_pos J _ hu t) H _ (efectivos_pos _ hu)
    · intro H j zero
      have e:=masa_en_lleno H u j
      rw [zero] at e; exact (normalizadorCero_pos H _ hu j).ne' e.symm
  · rw [coloresDelPerfil,if_neg hh]
    let x:=fraccionHuecos n h
    let u:=pesosMalla n x p
    have xp : 0<x := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hh) (by exact_mod_cast hn)
    have hu:=factores_positivos hn sp kp x xp
    apply soporte_desde_historias P (sameColors u) rfl
    · intro H; rw [peso_fisico_comun H h rfl u]
      exact masaRamaCon_pos _ (fun J t => positivo J _ hu t) H _ hu
    · intro H j zero
      have e:=masa_comun H h u j
      rw [zero] at e; exact (positivo H _ hu j).ne' e.symm

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_positiva_en_cada_tablero
