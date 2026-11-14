import RepresentanteFisicoDeLosCuatroLimites
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Set Filter MeasureTheory Perfil
open scoped Topology
def densidadDelExtremo (p : FactoresContinuos) (b : ℝ) (z : ℝ×ℝ) :=
  (b*pesoContinuo p z.1 z.2).toNNReal
def ocupacionDelExtremo (p : FactoresContinuos) (i : Fin 4) (s : ℝ) :=
  (1-holguraLinea p 0 i s).toNNReal

theorem producto_continuo_en_el_plano {p : FactoresContinuos} (cp : ∀ i,Continuous (camposFisicos p i)) (b : ℝ) :
    Continuous (fun z : ℝ×ℝ=>b*pesoContinuo p z.1 z.2) :=
  continuous_const.mul (((((cp 0).comp continuous_fst).mul ((cp 1).comp continuous_snd)).mul
    ((cp 2).comp (continuous_fst.sub continuous_snd))).mul ((cp 3).comp (continuous_fst.add continuous_snd)))

theorem ocupacion_limite_sin_truncar {P : ℕ→TableroMedido} {p : ℕ→FactoresContinuos} {b : ℕ→ℝ} {x : ℕ→ℝ≥0}
    {p₀ : FactoresContinuos} (eq : ∀ j,EulerFisica (P j) (p j) (x j) (b j))
    (zx : Tendsto (fun j=>(x j:ℝ)) atTop (𝓝 0))
    (lc : ∀ i,∀ s∈rangoF i,Tendsto (fun j=>camposFisicos (p j) i s) atTop (𝓝 (camposFisicos p₀ i s))) (i : Fin 4) :
    ∀ᵐ s ∂marginalRef i,Tendsto (fun j=>((P j).m i s:ℝ)) atTop (𝓝 (1-holguraLinea p₀ 0 i s)) ∧
      (ocupacionDelExtremo p₀ i s:ℝ)=1-holguraLinea p₀ 0 i s := by
  filter_upwards [linea_en_dominio i,ae_all_iff.mpr (fun j=>(eq j).linea i)] with s hs lines
  have times : Tendsto (fun j=>if i.val<2 then (x j:ℝ) else 1) atTop (𝓝 (if i.val<2 then (0:ℝ) else 1)) := by
    by_cases c : i.val<2
    · simpa only [if_pos c] using zx
    · simp only [if_neg c]; exact tendsto_const_nhds
  have hlim : Tendsto (fun j=>((P j).m i s:ℝ)) atTop (𝓝 (1-holguraLinea p₀ 0 i s)) := by
    apply (tendsto_const_nhds.sub (times.mul (lc i s hs))).congr
    intro j
    have l:=lines j
    change 1-((P j).m i s:ℝ)=holguraLinea (p j) (x j) i s at l
    change 1-holguraLinea (p j) (x j) i s=((P j).m i s:ℝ)
    linarith only [l]
  exact ⟨hlim,Real.coe_toNNReal _ (ge_of_tendsto hlim (Eventually.of_forall (fun _=>NNReal.coe_nonneg _)))⟩

theorem densidad_limite_del_producto {P : ℕ→TableroMedido} {p : ℕ→FactoresContinuos} {b : ℕ→ℝ}
    {x : ℕ→ℝ≥0} {p₀ : FactoresContinuos} {b₀ : ℝ} (bp : 0<b₀)
    (eq : ∀ j,EulerFisica (P j) (p j) (x j) (b j)) (bl : Tendsto b atTop (𝓝 b₀))
    (lc : ∀ i,∀ s∈rangoF i,Tendsto (fun j=>camposFisicos (p j) i s) atTop (𝓝 (camposFisicos p₀ i s))) :
    ∀ᵐ z ∂cuadrado,Tendsto (fun j=>((P j).ν z:ℝ)) atTop (𝓝 (densidadDelExtremo p₀ b₀ z:ℝ)) := by
  filter_upwards [tablero_en_dominio,ae_all_iff.mpr (fun j=>(eq j).real)] with z hz real
  have hf i:=lc i (coord i z) (coordenadas_en_dominio hz i)
  have val:=bl.mul ((((hf 0).mul (hf 1)).mul (hf 2)).mul (hf 3))
  have nn : 0≤b₀*pesoContinuo p₀ z.1 z.2 := by unfold pesoContinuo; positivity
  change Tendsto _ _ (𝓝 (((b₀*pesoContinuo p₀ z.1 z.2).toNNReal):ℝ))
  rw [Real.coe_toNNReal _ nn]
  exact val.congr (fun j=>(real j).symm)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.producto_continuo_en_el_plano
#print axioms ArticuloA.Historias.ocupacion_limite_sin_truncar
#print axioms ArticuloA.Historias.densidad_limite_del_producto
