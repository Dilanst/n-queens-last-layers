import EscalaDeReservaDeN3A2
namespace ArticuloA.Historias

/-- Control determinista del único normalizador q/X utilizado en las cuatro familias. -/
theorem control_del_normalizador {n q X τ t σ : ℝ}
    (qn : 0<q) (half : n≤2*q) (cap : q≤n) (pt : 0≤τ) (tiny : τ≤1/8)
    (hs : σ≤1) (tn : 0≤t) (ht : t≤σ/100) (loss : X≤q)
    (dev : |X-(1-τ)^2*q|≤n*t) :
    0<X ∧ 1≤q/X ∧ q/X≤2 ∧ q-X≤(2*τ+t)*n ∧ ((1-τ)^2-2*t)*q≤X := by
  have lower := (abs_le.mp dev).1
  have tnq:=mul_le_mul_of_nonneg_right half tn
  have sq : (49/64:ℝ)≤(1-τ)^2 := by
    nlinarith only [mul_nonneg (show 0≤1/8-τ by linarith) (show 0≤15/8-τ by linarith)]
  have key : ((1-τ)^2-2*t)*q≤X := by linarith only [lower,tnq]
  have hhalf : (1/2:ℝ)≤(1-τ)^2-2*t := by linarith only [sq,ht,hs]
  have hh := (mul_le_mul_of_nonneg_right hhalf qn.le).trans key
  have xp : 0<X := by linarith only [hh,qn]
  have term:=mul_le_mul_of_nonneg_left cap (show 0≤2*τ by linarith)
  refine ⟨xp,(le_div_iff₀ xp).mpr (by simpa using loss),(div_le_iff₀ xp).mpr (by linarith only [hh]),?_,key⟩
  nlinarith only [lower,term,mul_nonneg (sq_nonneg τ) qn.le]

theorem fila_conserva_holgura_al_normalizar {q X τ t σ M Y : ℝ}
    (qn : 0<q) (xp : 0<X) (tiny : τ≤1/8) (s0 : 0≤σ) (s1 : σ≤1)
    (tn : 0≤t) (ht : t≤σ/100) (key : ((1-τ)^2-2*t)*q≤X)
    (massa : M≤1-σ/2) (ret : Y≤(1-τ)^2*M+t) : (q/X)*Y ≤ 1-σ/4 := by
  have sq : (49/64:ℝ)≤(1-τ)^2 := by
    nlinarith only [mul_nonneg (show 0≤1/8-τ by linarith) (show 0≤15/8-τ by linarith)]
  have upper:=mul_le_mul_of_nonneg_left massa (sq_nonneg (1-τ))
  have threshold : Y≤(1-σ/4)*((1-τ)^2-2*t) := by
    nlinarith only [ret,upper,mul_le_mul_of_nonneg_right sq s0,ht,s0,mul_nonneg s0 tn]
  have ta:=mul_le_mul_of_nonneg_right threshold qn.le
  have tb:=mul_le_mul_of_nonneg_left key (show 0≤1-σ/4 by linarith)
  rw [div_mul_eq_mul_div,div_le_iff₀ xp]
  linarith only [ta,tb]

theorem oblicua_conserva_holgura_al_normalizar {q X τ t σ L M Y : ℝ}
    (qn : 0<q) (xp : 0<X) (pt : 0≤τ) (tiny : τ≤L/8) (s0 : 0≤σ) (sl : σ≤L) (l1 : L≤1)
    (tn : 0≤t) (ht : t≤σ/100) (key : ((1-τ)^2-2*t)*q≤X)
    (massa : M≤1-3*L/4) (ret : Y≤(1-τ)*M+t) : (q/X)*Y ≤ 1-σ/4 := by
  let u:=1-τ
  have ulo : (7/8:ℝ)≤u := by dsimp [u]; linarith only [tiny,l1]
  have up : 0≤u := (by norm_num : (0:ℝ)≤7/8).trans ulo
  have upper:=mul_le_mul_of_nonneg_left massa up
  have inside : 3*L/8 ≤ (3*L-σ)/4-τ*(1-σ/4) := by
    nlinarith only [sl,tiny,mul_nonneg pt s0]
  have grow:=mul_le_mul_of_nonneg_left inside up
  have grow' := mul_le_mul_of_nonneg_right ulo (show 0≤3*L/8 by linarith)
  have threshold : Y≤(1-σ/4)*((1-τ)^2-2*t) := by
    dsimp [u] at upper grow grow'
    nlinarith only [ret,upper,grow,grow',ht,sl,s0,mul_nonneg s0 tn]
  have ta:=mul_le_mul_of_nonneg_right threshold qn.le
  have tb:=mul_le_mul_of_nonneg_left key (show 0≤1-σ/4 by linarith)
  rw [div_mul_eq_mul_div,div_le_iff₀ xp]
  linarith only [ta,tb]

end ArticuloA.Historias
#print axioms ArticuloA.Historias.control_del_normalizador
#print axioms ArticuloA.Historias.fila_conserva_holgura_al_normalizar
#print axioms ArticuloA.Historias.oblicua_conserva_holgura_al_normalizar
