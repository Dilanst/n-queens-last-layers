import VisitasSimultaneasALasReservasFijas
import SoporteDeLasHistoriasDelProcesoGuiado
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

open Classical

def marcasDeG {n} (D A : ℤ→Prop) (z e : Cell n) : Prop :=
  ∀ y∈([ (corners (z,e)).1,(corners (z,e)).2 ] : List (Cell n)),D (llaveDeLinea 2 y) ∧ A (llaveDeLinea 3 y)

def salidaFisicaDeG {n} (m : ℕ) (D A : ℤ→Prop) (hist : List (EstadoGuiado n)) : Prop :=
  ∃ v,ultimoEstado (some ([] : List (Cell n))) hist=some v ∧
    SalidaDeReserva m D A (elegirCasillas v.toFinset (board n))

theorem camino_con_marcas_da_salida {n m q} (ρ : Cell n→ℝ≥0) (D A : ℤ→Prop) (d : ℝ≥0)
    (sum : q+m=n) (evita : ∀ e,ρ e≠0 → ¬D (llaveDeLinea 2 e) ∧ ¬A (llaveDeLinea 3 e))
    (i : ℝ≥0×List (EstadoGuiado n)) (hi : i∈rutas (pasoDeG ρ q) 0 q (some []))
    (ok : prefijoRegular (condicionDeSeguimientoG ρ q (marcasDeG D A) d) 0 (some []) i.2)
    (hits : ∀ z,9*m+3≤visitasDeCamino (fun _ _ y=>observaCabeza (marcasDeG D A z) y) 0 (some []) i.2) :
    salidaFisicaDeG m D A i.2 := by
  obtain ⟨path,len⟩:=rutas_siguen_su_ley _ _ _ _ _ hi
  obtain ⟨v,ev,legal,supp,sz,counts⟩:=terminal_regular_de_G ρ q (marcasDeG D A) d 0 [] i.2
    .nil (by simp) path ok
  have uniq : v.Nodup:=legal.imp (fun h eq=>h.1 (congrArg Prod.fst eq))
  have pw : (v.toFinset : Set (Cell n)).Pairwise compatible:=
    (List.pairwise_iff_coe_toFinset_pairwise uniq
      (fun a b (h : compatible a b)=>⟨h.1.symm,h.2.1.symm,h.2.2.1.symm,h.2.2.2.symm⟩)).mpr legal
  refine ⟨v,ev,(legal_iff_pares_del_soporte _).mpr (by rwa [soporte_elegido]),?_,?_,?_⟩
  · rw [←tamano_soporte,soporte_elegido,List.toFinset_card_of_nodup uniq,sz,len]; simpa using sum
  · intro e he
    exact evita e (supp e (by simpa using (mem_elegidas _ _ _).mp he |>.1))
  · intro z
    have c:=counts (marcasDeG D A z)
    simp only [List.toFinset_nil,Finset.filter_empty,Finset.card_empty,zero_add] at c
    have lower := (hits z).trans_eq c.symm
    have sets : candidatasDeReserva (elegirCasillas v.toFinset (board n)) z D A=v.toFinset.filter (marcasDeG D A z):=by
      ext e
      simp [candidatasDeReserva,soporte_elegido,marcasDeG]
    rw [sets]
    exact lower

theorem fallo_geometrico_en_origenes_regulares {n m q} (ρ : Cell n→ℝ≥0) (D A : ℤ→Prop) (d : ℝ≥0)
    (sum : q+m=n) (evita : ∀ e,ρ e≠0 → ¬D (llaveDeLinea 2 e) ∧ ¬A (llaveDeLinea 3 e))
    (prob : (3/4:ℝ≥0)*d≤1) (umbral : ((9*m+2:ℕ):ℝ)≤(((3/4:ℝ≥0)*d):ℝ)*q/3) :
    (avg masas (rutas (pasoDeG ρ q) 0 q (some [])) (mark masas (fun l=>
      prefijoRegular (condicionDeSeguimientoG ρ q (marcasDeG D A) d) 0 (some []) l ∧
      ¬salidaFisicaDeG m D A l))).val ≤ (n:ℝ)^2*exp (-(((3/4:ℝ≥0)*d):ℝ)*q/6) := by
  let V:=condicionDeSeguimientoG ρ q (marcasDeG D A) d
  let I (z : Cell n) (_ : ℕ) (_ y : EstadoGuiado n):=observaCabeza (marcasDeG D A z) y
  let law:=rutas (pasoDeG ρ q) 0 q (some [])
  let F (l : List (EstadoGuiado n)):=prefijoRegular V 0 (some []) l ∧ ¬salidaFisicaDeG m D A l
  let B (l : List (EstadoGuiado n)):=∃ z,prefijoRegular V 0 (some []) l ∧ visitasDeCamino (I z) 0 (some []) l≤9*m+2
  have mono:=avg_mono masas law (mark masas F) (mark masas B) (by
    intro i hi
    by_cases h : F i.2
    · have b : B i.2:=by
        by_contra away
        apply h.2
        apply camino_con_marcas_da_salida ρ D A d sum evita i hi h.1
        intro z
        have miss : ¬visitasDeCamino (I z) 0 (some []) i.2≤9*m+2:=fun low=>away ⟨z,h.1,low⟩
        exact Nat.succ_le_of_lt (lt_of_not_ge miss)
      simp [mark,h,b,masas]
    · simp [mark,h,masas])
  exact (NNReal.coe_le_coe.mpr mono).trans (cola_simultanea_por_las_raices (G_es_ley ρ q) V I _ prob
    (deriva_de_las_visitas_de_G ρ (marcasDeG D A) d) q 0 (9*m+2) (some []) umbral)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.camino_con_marcas_da_salida
#print axioms ArticuloA.Historias.fallo_geometrico_en_origenes_regulares
