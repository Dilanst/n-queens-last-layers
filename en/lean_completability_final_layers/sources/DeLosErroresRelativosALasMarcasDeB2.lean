import ErrorFisicoYSeguridadDeCadaPadre
namespace ArticuloA.Historias
open Repair RealFinita Trayectoria Trayectoria.ProfileKernel Real
open scoped NNReal BigOperators
noncomputable section
open Classical

theorem costo_de_una_marca_en_funcion_del_error {η q cw cz R A E : ℝ} (hp : 0<η) (h1 : η≤1)
    (qp : 0<q) (wn : 0≤cw) (zn : 0≤cz) (rn : 0≤R) (ae : A≤E)
    (budget : cw/q+cz+(22/10)*q*R≤A) :
    cw/q+(11/10)*(4*E/((9/10)*η)+q*R)≤8*E/η := by
  have u : 0≤cw/q:=div_nonneg wn qp.le
  have r : 0≤q*R:=mul_nonneg qp.le rn
  have en : 0≤E:=by linarith only [budget,ae,r,u,zn]
  have w : cw/q≤E:=by linarith only [budget,ae,r,zn]
  have z : q*R≤E:=by linarith only [budget,ae,r,u,zn]
  have m : E≤E/η:=(le_div_iff₀ hp).mpr (mul_le_of_le_one_right en h1)
  have eq : 4*E/((9/10)*η)=(40/9)*(E/η):=by field_simp; ring
  rw [eq,mul_div_assoc]
  linarith only [w,z,m,div_nonneg en hp.le]

theorem observacion_de_un_conjunto_marcado {I : Type} {n q t} (v : Cell n→ℝ≥0) (l : List (Cell n))
    (f : I→Cell n→ℝ) (j : I) (S : Cell n→Prop)
    (repr : ∀ e,f j e=(mark masas S e).val) (pos : ∀ e i,0<fraccionVivaG v q t e i) :
    observacionFisica v q f (.inl j) t l=(avg masas (opcionesGuiadas v q t l) (mark masas S)).val := by
  rw [←media_coe,observable_real_sobre_las_opciones]
  simp only [observacionFisica]
  congr 1
  funext e
  rw [repr,cuatro_familias_dan_el_peso_de_G v q t e (fun i=>(pos e i).le)]
  rfl

theorem condicion_B2_de_las_desviaciones {n q t} (v : Cell n→ℝ≥0) (qp : 0<q) (l : List (Cell n))
    (S : Cell n→Cell n→Prop) (d : ℝ≥0) {E : ℝ} (small : E≤1/80) (err : sigueTableroYLineas v q t l E)
    (marks : ∀ z,(d:ℝ)*q≤∑ e,(v e:ℝ)*(mark masas (S z) e).val)
    (accuracy : ∀ z,|(avg masas (opcionesGuiadas v q t l) (mark masas (S z))).val-
      (∑ e,(v e:ℝ)*(mark masas (S z) e).val)|/(q:ℝ)≤(d:ℝ)/16) :
    condicionDeSeguimientoG v q S d t (some l) := by
  have qr : 0<(q:ℝ):=by exact_mod_cast qp
  have w:=(abs_le.mp ((div_le_iff₀ qr).mp (err.1.trans small)))
  have lo : 0<tableroG v q t l:=by linarith only [w.1,qr]
  have hi : tableroG v q t l≤(81/80:ℝ)*q:=by linarith only [w.2]
  refine ⟨by exact_mod_cast lo,?_,?_⟩
  · apply NNReal.coe_le_coe.mp
    push_cast
    exact hi
  · intro z
    apply NNReal.coe_le_coe.mp
    push_cast
    have low:=(abs_le.mp ((div_le_iff₀ qr).mp (accuracy z))).1
    change (15/16:ℝ)*(d:ℝ)*(q:ℝ)≤(avg masas (opcionesGuiadas v q t l) (mark masas (S z))).val
    nlinarith only [marks z,low]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.costo_de_una_marca_en_funcion_del_error
#print axioms ArticuloA.Historias.condicion_B2_de_las_desviaciones
