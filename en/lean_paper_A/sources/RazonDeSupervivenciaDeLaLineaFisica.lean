import ErrorFisicoYSeguridadDeCadaPadre
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

def lineaVivaEnEstado {n} (i : Fin 4) (z : Cell n) : EstadoGuiado n→Prop
  | none=>False
  | some l=>∀ e∈l,llaveDeLinea i e≠llaveDeLinea i z

theorem masa_fisica_de_supervivencia_en_un_paso {n q t} (v : Cell n→ℝ≥0) (l : List (Cell n))
    (reg : total masas (opcionesGuiadas v q t l)≠0) (i : Fin 4) (z : Cell n) (live : lineaVivaEnEstado i z (some l)) :
    (avg masas (pasoDeG v q t (some l)) (mark masas (lineaVivaEnEstado i z))).val=
      1-riesgoDeLinea (leyDePieza v q t l) z i := by
  rw [←media_coe,media_del_paso_fisico v q t l reg,←ley_de_pieza_normalizada v q t l reg,riesgoDeLinea,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  have keep : lineaVivaEnEstado i z (some (b::l))↔llaveDeLinea i b≠llaveDeLinea i z:=by
    constructor
    · intro ok; exact ok b List.mem_cons_self
    · intro nb a ha; rcases List.mem_cons.mp ha with rfl|inl; exact nb; exact live a inl
  by_cases eq : llaveDeLinea i b=llaveDeLinea i z <;> simp [mark,keep,eq,masas]

theorem factor_de_supervivencia_con_error {p u H : ℝ} (small : u≤1/2) (hn : 0≤H) (err : |p-u|≤H) :
    1-p≤(1-u)*exp (2*H) := by
  have e:=mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2*H)) (show 0≤1-u by linarith)
  have sh:=mul_nonneg (sub_nonneg.mpr small) hn
  have lo:=(abs_le.mp err).1
  nlinarith only [e,sh,lo]

theorem razon_entre_holguras_consecutivas {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (z : Cell n) (i : Fin 4)
    (pos : 0<fraccionVivaG v q t z i) :
    1-riesgoPrevisto v q t z i=fraccionVivaG v q (t+1) z i/fraccionVivaG v q t z i := by
  have qr : (q:ℝ)≠0:=by exact_mod_cast qp.ne'
  apply (eq_div_iff pos.ne').mpr
  have eq : riesgoPrevisto v q t z i*fraccionVivaG v q t z i=(masaDeLineaG v i z:ℝ)/q:=by
    unfold riesgoPrevisto
    rw [←div_div,div_mul_cancel₀ _ pos.ne']
  rw [sub_mul,one_mul,eq]
  unfold fraccionVivaG
  push_cast
  ring
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.masa_fisica_de_supervivencia_en_un_paso
#print axioms ArticuloA.Historias.factor_de_supervivencia_con_error
