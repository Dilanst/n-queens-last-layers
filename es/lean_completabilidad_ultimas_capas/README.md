# Formalización en Lean

Esta carpeta contiene la formalización en Lean 4 de los resultados principales de

- **[A]** D. S. Mejia, *Completabilidad de las últimas capas en el problema de las n reinas*, 2026. Repositorio: [n-queens-last-layers](https://github.com/Dilanst/n-queens-last-layers).

La Sección 12 de [A] precisa qué comprueba la formalización y qué no.

## El teorema final

```
ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos : ConclusionDelArticuloA
```

El teorema está en `fuentes/CierreDeLosSeisBloquesDelArticuloA.lean`, y su enunciado, `ConclusionDelArticuloA`, en `fuentes/PrimerOrdenDeLasSalidasConReserva.lean`. No tiene hipótesis. Afirma que existen una familia de perfiles, indexada por x ∈ [0, 1/2], y constantes κ, M y L tales que:

1. la familia cumple la ecuación de Euler del perfil con masa 1 − x (`EulerFisica`);
2. sus cuatro factores toman valores en [κ, M] y son L-Lipschitz, con las mismas constantes para todo x (`ControlEspacial`);
3. en x = 0 cumple la normalización ∫r_R = ∫r_C = 1 (`NormalizacionR15`);
4. en x = 0 maximiza el funcional entre las densidades admisibles de masa uno (`IsGreatest valoresAdmisiblesLlenos …`);
5. cumple las doce conclusiones de `ResultadosDeCapas` (`fuentes/ConclusionesDelArticuloEnUnSoloPerfil.lean`).

Todas las conclusiones se refieren a la misma familia.

### Correspondencia con [A]

| Campo de `ResultadosDeCapas` | Resultado de [A] | Observación |
|---|---|---|
| `limite`, `uniformeFijo` | Teorema 1.1 | Incluye la forma uniforme en 1 ≤ h ≤ K |
| `cociente` | Corolario 1.2 | La equivalencia asintótica |
| `residual` | Corolario 1.3 | Con F((h − σ)/n) para todo σ ∈ [0, 1] |
| `positiva`, `pisoExplicito` | Teorema 1.4 | Con un κ existencial |
| `porCruce`, `espacial`, `sinPeso` | Teorema 1.5 (a), (b), (c) | |
| `entropia` | Teorema 3.6 | Versión formal, con una cota o(n) |
| `inversa` | Proposición 8.3 | Con el peso w = 1/a |
| `reparacion` | Sección 7 | Con una constante existencial |

## Cómo compilarla

Hace falta [elan](https://github.com/leanprover/elan), que instala la versión de Lean indicada en `lean-toolchain` (4.19.0), y git. Desde esta carpeta:

```
lake exe cache get                # descarga Mathlib ya compilado (revisión c44e0c8)
lake build                        # compila los 659 módulos; las advertencias cuentan como errores
lake env lean Comprobacion.lean   # muestra el teorema final y sus axiomas
```

La salida termina con

```
'ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos' depends on axioms: [propext, Classical.choice, Quot.sound]
```

es decir, el teorema sólo usa los tres axiomas habituales de Lean.

**Sin Lake.** `verificar.py` usa un ejecutable de Lean 4.19.0 y una copia local de Mathlib ya compilada. Primero comprueba las huellas de `fuentes.sha256`; después compila los módulos uno a uno y termina con la lista de axiomas:

```
python verificar.py --solo-inventario
python verificar.py --lean RUTA/AL/lean --mathlib RUTA/A/mathlib4
```

## Comprobación independiente

[lean4checker](https://github.com/leanprover/lean4checker) vuelve a pasar por el núcleo de Lean todas las declaraciones de las que depende el teorema final, también las de Mathlib:

```
git clone --depth 1 --branch v4.19.0 https://github.com/leanprover/lean4checker
(cd lean4checker && lake build)
lake env lean4checker/.lake/build/bin/lean4checker --fresh CierreDeLosSeisBloquesDelArticuloA
```

En `.github/workflows/` hay dos flujos de GitHub Actions que repiten en Linux, desde cero, la compilación (`compilar.yml`, en cada envío) y esta comprobación (`lean4checker.yml`, que se lanza a mano). GitHub sólo los ejecuta cuando esta carpeta es la raíz del repositorio.

## Alcance

- **Identificación con el perfil de [A].** Usa que el maximizador es único. Esa unicidad está demostrada en [P], pero no está formalizada aquí.
- **F(0) = 1/b₀.** Es una definición, no un resultado.
- **Teoremas 2.2 y 2.3 de [A].** La formalización no los toma como hipótesis: construye la familia de perfiles y demuestra por su cuenta la cota inferior de primer orden para log Q(n), por un camino distinto del del artículo. Ese camino está en los módulos cuyo nombre contiene `Reserva`, `Historias` o `E2`, y su enunciado final, en `fuentes/PrimerOrdenDeLasSalidasConReserva.lean`.
- **Lo que no comprueba:** la demostración escrita de [A], sus constantes explícitas ni sus valores numéricos.

**[P]** D. S. Mejia, *El perfil variacional de las colocaciones parciales de reinas: existencia, ecuaciones de Euler y regularidad hasta el tablero lleno*, 2026. DOI: [10.5281/zenodo.24220042](https://doi.org/10.5281/zenodo.24220042). Repositorio: [n-queens-variational-profile](https://github.com/Dilanst/n-queens-variational-profile).

## Nombres

Algunos módulos y teoremas conservan en el nombre etiquetas de trabajo, como DEF, E2, B1, B2, R5, R7, R15 o N3A2. No remiten a ningún texto publicado; lo que hace cada módulo se lee en sus enunciados.

## Licencia

[MIT](LICENSE).
