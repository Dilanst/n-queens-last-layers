import PrimerOrdenDeLasSalidasConReserva
import PrefijosDeUnaMismaTrayectoria
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

open Classical
abbrev EstadoGuiado (n : ℕ) := Option (List (Cell n))

def masaDeLineaG {n} (ρ : Cell n→ℝ≥0) (i : Fin 4) (e : Cell n) : ℝ≥0 :=
  ∑ c : Cell n,if llaveDeLinea i c=llaveDeLinea i e then ρ c else 0

def pesoGuiado {n} (ρ : Cell n→ℝ≥0) (q t : ℕ) (e : Cell n) : ℝ≥0 :=
  ρ e / ∏ i : Fin 4, (1-(t:ℝ≥0)/q*masaDeLineaG ρ i e)

def opcionesGuiadas {n} (ρ : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n)) : Atoms ℝ≥0 (Cell n) :=
  ((board n).filter (fun e=>decide (ρ e ≠ 0 ∧ ∀ c∈l,compatible e c))).map (fun e=>(pesoGuiado ρ q t e,e))

def pasoDeG {n} (ρ : Cell n→ℝ≥0) (q t : ℕ) : EstadoGuiado n→Atoms ℝ≥0 (EstadoGuiado n)
  | none=>point masas none
  | some l=>ProfileKernel.choose masas ((opcionesGuiadas ρ q t l).map (fun i=>(i.1,some (i.2::l)))) none (·⁻¹)

def observaCabeza {n} (S : Cell n→Prop) : EstadoGuiado n→Prop
  | some (e::_)=>S e
  | _=>False

theorem G_es_ley {n} (ρ : Cell n→ℝ≥0) (q t : ℕ) (x : EstadoGuiado n) : total masas (pasoDeG ρ q t x)=1 := by
  cases x with
  | none=>exact avg_point masas _ _
  | some l=>exact choose_total masas _ _ (·⁻¹) (fun _ nz=>inv_mul_cancel₀ nz)

theorem G_pone_una_reina_con_probabilidad_V_sobre_W {n} (ρ : Cell n→ℝ≥0) (q t : ℕ) (l : List (Cell n))
    (S : Cell n→Prop) (hW : total masas (opcionesGuiadas ρ q t l)≠0) :
    avg masas (pasoDeG ρ q t (some l)) (mark masas (observaCabeza S))=
       avg masas (opcionesGuiadas ρ q t l) (mark masas S)/total masas (opcionesGuiadas ρ q t l) := by
  let row:=opcionesGuiadas ρ q t l
  let put (e : Cell n) : EstadoGuiado n:=some (e::l)
  have mass : total masas (row.map (fun i=>(i.1,put i.2)))=total masas row:=avg_push masas row put _
  change avg masas (ProfileKernel.choose masas (row.map (fun i=>(i.1,put i.2))) none (·⁻¹)) _=_
  unfold ProfileKernel.choose
  split
  · rename_i h
    exact False.elim (hW (mass.symm.trans h))
  · rw [avg_scale,mass,avg_push masas row put]
    exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm

def condicionDeSeguimientoG {n} (ρ : Cell n→ℝ≥0) (q : ℕ) (U : Cell n→Cell n→Prop) (d : ℝ≥0)
    (t : ℕ) : EstadoGuiado n→Prop
  | none=>False
  | some l=>let row:=opcionesGuiadas ρ q t l
            0<total masas row ∧ total masas row≤(81/80:ℝ≥0)*q ∧
            ∀ z,(15/16:ℝ≥0)*d*q≤avg masas row (mark masas (U z))

theorem deriva_de_las_visitas_de_G {n} (ρ : Cell n→ℝ≥0) {q : ℕ} (U : Cell n→Cell n→Prop)
    (d : ℝ≥0) (z : Cell n) (t : ℕ) (x : EstadoGuiado n)
    (ok : condicionDeSeguimientoG ρ q U d t x) :
    (3/4:ℝ≥0)*d ≤ avg masas (pasoDeG ρ q t x) (mark masas (observaCabeza (U z))) := by
  cases x with
  | none=>exact False.elim ok
  | some l=>
    obtain ⟨pos,top,bottom⟩:=ok
    rw [G_pone_una_reina_con_probabilidad_V_sobre_W _ _ _ _ _ pos.ne']
    apply (le_div_iff₀ pos).mpr
    calc
      _ ≤ ((3/4:ℝ≥0)*d)*((81/80:ℝ≥0)*q) := mul_le_mul_of_nonneg_left top (zero_le _)
      _ = (243/320:ℝ≥0)*(d*q) := by apply NNReal.eq; push_cast; ring
      _ ≤ (15/16:ℝ≥0)*(d*q) := mul_le_mul_of_nonneg_right (by apply NNReal.coe_le_coe.mp; push_cast; norm_num) (zero_le _)
      _ ≤ _ := (mul_assoc _ _ _).ge.trans (bottom z)

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.G_es_ley
#print axioms ArticuloA.Historias.G_pone_una_reina_con_probabilidad_V_sobre_W
#print axioms ArticuloA.Historias.deriva_de_las_visitas_de_G
