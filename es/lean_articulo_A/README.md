# Formalización en Lean del Artículo A

Formalización en Lean 4 de los resultados principales de:

- **[A]** D. S. Mejia, *Completabilidad de las últimas capas en el problema de las n reinas*, 2026.

La Sección 12 de [A] describe con precisión qué comprueba esta formalización y qué no.

> **English summary.** This is a Lean 4 formalization of the main results of [A]. The final theorem, `ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos`, has no hypotheses. It depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. Toolchain: Lean 4.19.0 and Mathlib at commit `c44e0c8`. To build and check, run `lake exe cache get && lake build`, then `lake env lean Comprobacion.lean`.

## El teorema final

```
ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos : ConclusionDelArticuloA
```

Está en `fuentes/CierreDeLosSeisBloquesDelArticuloA.lean`; el enunciado `ConclusionDelArticuloA` se define en `fuentes/PrimerOrdenDeLasSalidasConReserva.lean`. Dice que existen una familia de perfiles, indexada por x ∈ [0, 1/2], y constantes κ, M y L tales que:

1. la familia cumple la ecuación de Euler del perfil con masa 1 − x (`EulerFisica`);
2. sus cuatro factores toman valores en [κ, M] y son L-Lipschitz, con constantes comunes a todo x (`ControlEspacial`);
3. en x = 0 cumple la normalización ∫r_R = ∫r_C = 1 (`NormalizacionR15`);
4. su término en x = 0 maximiza el funcional entre las densidades admisibles de masa uno (`IsGreatest valoresAdmisiblesLlenos …`);
5. valen las doce conclusiones de `ResultadosDeCapas` (`fuentes/ConclusionesDelArticuloEnUnSoloPerfil.lean`).

Todas las conclusiones se refieren a esa misma familia.

### Correspondencia con [A]

| Campo de `ResultadosDeCapas` | Resultado de [A] | Observación |
|---|---|---|
| `limite`, `uniformeFijo` | Teorema 1.1 | También la forma uniforme en 1 ≤ h ≤ K |
| `cociente` | Corolario 1.2 | La equivalencia asintótica |
| `residual` | Corolario 1.3 | Para todo s ∈ [0, 1] |
| `positiva`, `pisoExplicito` | Teorema 1.4 | Con un κ existencial |
| `porCruce`, `espacial`, `sinPeso` | Teorema 1.5 (a), (b), (c) | |
| `entropia` | Teorema 3.6 | Versión formal, con un presupuesto o(n) |
| `inversa` | Proposición 8.3 | Con el peso w = 1/a |
| `reparacion` | Sección 7 | Con una constante existencial |

## Compilar

Requisitos: [elan](https://github.com/leanprover/elan), que instala la versión de Lean indicada en `lean-toolchain`, y git.

```
lake exe cache get                # descarga Mathlib ya compilado (revisión c44e0c8)
lake build                        # compila los 659 módulos; las advertencias cuentan como errores
lake env lean Comprobacion.lean   # muestra el teorema final y sus axiomas
```

La salida termina con:

```
'ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos' depends on axioms: [propext, Classical.choice, Quot.sound]
```

El flujo `.github/workflows/compilar.yml` repite estos pasos en Linux, desde cero, en cada envío al repositorio.

**Sin Lake.** `verificar.py` usa un ejecutable de Lean 4.19.0 y una copia local ya compilada de Mathlib. Primero coteja las huellas de `fuentes.sha256`; luego compila los módulos uno a uno y termina con la lista de axiomas:

```
python verificar.py --solo-inventario
python verificar.py --lean RUTA/AL/lean --mathlib RUTA/A/mathlib4
```

## Comprobación independiente del núcleo

[lean4checker](https://github.com/leanprover/lean4checker) vuelve a pasar por el núcleo de Lean todas las declaraciones de las que depende el teorema final, incluidas las de Mathlib. El flujo `.github/workflows/lean4checker.yml` se lanza a mano. Los pasos equivalentes son:

```
git clone --depth 1 --branch v4.19.0 https://github.com/leanprover/lean4checker
(cd lean4checker && lake build)
lake env lean4checker/.lake/build/bin/lean4checker --fresh CierreDeLosSeisBloquesDelArticuloA
```

## Alcance

- **Identificación con el perfil de [A].** Usa la unicidad del maximizador. Está demostrada en [P], pero no está formalizada aquí.
- **F(0) = 1/b₀.** Es una definición.
- **Teoremas 2.2 y 2.3 de [A].** La formalización no los toma como hipótesis. Construye la familia y demuestra la cota inferior de primer orden para log Q(n) por una vía propia, distinta de la del artículo. Esa vía está en los módulos cuyo nombre contiene `Reserva`, `Historias` o `E2`; su enunciado final está en `fuentes/PrimerOrdenDeLasSalidasConReserva.lean`.
- **Lo que no comprueba:** la demostración escrita de [A], sus constantes explícitas y sus valores numéricos.

[P] D. S. Mejia, *El perfil variacional de las colocaciones parciales de reinas: existencia, ecuaciones de Euler y regularidad hasta el tablero lleno*, 2026.

## Nombres

Algunos nombres de módulos y de teoremas conservan etiquetas de trabajo, por ejemplo DEF, E2, B1, B2, R5, R7, R15 o N3A2. No remiten a ningún texto publicado; lo que hace cada módulo está en sus enunciados.

## Licencia

MIT (ver `LICENSE`).
