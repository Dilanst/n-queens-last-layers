# Lean formalization

This folder contains the Lean 4 formalization of the main results of

- **[A]** D. S. Mejia, *Completability of the final layers in the n-queens problem*, 2026. Repository: [n-queens-last-layers](https://github.com/Dilanst/n-queens-last-layers).

Section 12 of [A] states exactly what the formalization checks and what it does not.

The names of modules and theorems are in Spanish, as in [A]; the section [Names](#names) lists the most frequent words.

## The final theorem

```
ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos : ConclusionDelArticuloA
```

The theorem is in `sources/CierreDeLosSeisBloquesDelArticuloA.lean`, and its statement, `ConclusionDelArticuloA`, in `sources/PrimerOrdenDeLasSalidasConReserva.lean`. It has no hypotheses. It states that there exist a family of profiles, indexed by x ∈ [0, 1/2], and constants κ, M and L such that:

1. the family satisfies the Euler equation of the profile with mass 1 − x (`EulerFisica`);
2. its four factors take values in [κ, M] and are L-Lipschitz, with the same constants for every x (`ControlEspacial`);
3. at x = 0 it satisfies the normalization ∫r_R = ∫r_C = 1 (`NormalizacionR15`);
4. at x = 0 it maximizes the functional among the admissible densities of mass one (`IsGreatest valoresAdmisiblesLlenos …`);
5. it satisfies the twelve conclusions of `ResultadosDeCapas` (`sources/ConclusionesDelArticuloEnUnSoloPerfil.lean`).

All the conclusions refer to the same family.

### Correspondence with [A]

| Field of `ResultadosDeCapas` | Result in [A] | Remark |
|---|---|---|
| `limite`, `uniformeFijo` | Theorem 1.1 | Includes the uniform form over 1 ≤ h ≤ K |
| `cociente` | Corollary 1.2 | The asymptotic equivalence |
| `residual` | Corollary 1.3 | With F((h − σ)/n) for every σ ∈ [0, 1] |
| `positiva`, `pisoExplicito` | Theorem 1.4 | With an existential κ |
| `porCruce`, `espacial`, `sinPeso` | Theorem 1.5 (a), (b), (c) | |
| `entropia` | Theorem 3.6 | Formal version, with an o(n) bound |
| `inversa` | Proposition 8.3 | With the weight w = 1/a |
| `reparacion` | Section 7 | With an existential constant |

## How to build it

You need [elan](https://github.com/leanprover/elan), which installs the Lean version given in `lean-toolchain` (4.19.0), and git. From this folder:

```
lake exe cache get          # downloads the precompiled Mathlib (revision c44e0c8)
lake build                  # builds the 659 modules; warnings count as errors
lake env lean Check.lean    # prints the final theorem and its axioms
```

The output ends with

```
'ArticuloA.Historias.conclusion_del_articulo_A_para_los_tableros_fisicos' depends on axioms: [propext, Classical.choice, Quot.sound]
```

that is, the theorem uses only the three standard axioms of Lean.

**Without Lake.** `verify.py` uses a Lean 4.19.0 executable and a local copy of Mathlib that is already built. It first checks the hashes in `sources.sha256`; it then builds the modules one by one and ends with the list of axioms:

```
python verify.py --inventory-only
python verify.py --lean PATH/TO/lean --mathlib PATH/TO/mathlib4
```

## Independent check

[lean4checker](https://github.com/leanprover/lean4checker) replays through the Lean kernel every declaration the final theorem depends on, including those of Mathlib:

```
git clone --depth 1 --branch v4.19.0 https://github.com/leanprover/lean4checker
(cd lean4checker && lake build)
lake env lean4checker/.lake/build/bin/lean4checker --fresh CierreDeLosSeisBloquesDelArticuloA
```

`.github/workflows/` contains two GitHub Actions workflows that repeat on Linux, from scratch, the build (`build.yml`, on every push) and this check (`lean4checker.yml`, started by hand). GitHub runs them only when this folder is the root of the repository.

## Scope

- **Identification with the profile of [A].** It uses the fact that the maximizer is unique. That uniqueness is proved in [P], but it is not formalized here.
- **F(0) = 1/b₀.** This is a definition, not a result.
- **Theorems 2.2 and 2.3 of [A].** The formalization does not take them as hypotheses: it constructs the family of profiles and proves the first-order lower bound for log Q(n) on its own, by a route different from that of the paper. That route is in the modules whose names contain `Reserva`, `Historias` or `E2`, and its final statement is in `sources/PrimerOrdenDeLasSalidasConReserva.lean`.
- **What it does not check:** the written proof of [A], its explicit constants or its numerical values.

**[P]** D. S. Mejia, *The variational profile of partial queen placements: existence, Euler equations, and regularity up to the full board*, 2026. Repository: [n-queens-variational-profile](https://github.com/Dilanst/n-queens-variational-profile).

## Names

Some modules and theorems keep working labels in their names, such as DEF, E2, B1, B2, R5, R7, R15 or N3A2. They do not refer to any published text; what each module does can be read from its statements.

Frequent words in the names: *articulo* (paper), *capa* (layer), *casilla* (square), *tablero* (board), *lleno* (full), *fisico* (physical), *perfil* (profile), *fibra* (fiber), *cota* (bound), *conteo* (count), *ley* (law), *historia* (history), *reserva* (reserve), *salida* (output or exit), *marca* (mark), *absorbedor* (absorber), *inversa* (reverse), *reparacion* (repair), *hueco* (hole), *holgura* (slack), *deriva* (drift).

## License

[MIT](LICENSE).
