# Grados26Learning

Manuscrito formalizado en el commit [`3f8749bfbb5ee2c3d1eefa646724fb6c043018cf`](https://github.com/wbgradost/ai-project/blob/3f8749bfbb5ee2c3d1eefa646724fb6c043018cf/paper/paper.pdf).
La carpeta [Grados26Learning](Grados26Learning/) se recuperó del worktree de
AppliedModelingLib sobre la revisión `194edcc95df74806a39b961d10dedddc6e730cce` y se comprobó con Lean
`4.30.0-rc2`.

| Resultado | Declaración y archivo | Alcance comprobado |
|---|---|---|
| Lema 1 | `Grados26Learning.lemma1` · `WorkerResult.lean` | Mayor maximizador y condiciones de interior y esquina. |
| Lema 2 | `Grados26Learning.lemma2` · `CTMCResult.lean` | Ley estacionaria única, transición y esperanza de ocupación. |
| Proposición 1 | `Grados26Learning.proposition1` · `ShapeResult.lean` | Regímenes, umbrales, saturación y curvatura. |
| Proposición 2 | `Grados26Learning.proposition2` · `ComparisonResult.lean` | Comparaciones, igualdad, saturación, dominancia y habilidad media. |
| Corolario 1 | `Grados26Learning.corollary1` · `SensitivityResult.lean` | Sensibilidades, ganancias y escala temporal. |

El [registro oficial](Grados26Learning/paper-scoped-check.txt) conserva
la salida de `python3 scripts/paper_contribution.py check Grados26Learning --fast`.
La [comprobación de declaraciones y axiomas](Grados26Learning/proof-kernel-check.txt)
documenta los resultados que se cargaron en una sesión nueva.

La [ejecución sin ajustes](Grados26Learning/paper-scoped-check-upstream.txt)
compiló la interfaz y agotó el tiempo del lector de dependencias. La
ejecución completa usó importaciones modulares en el lector generado y
conservó la validación nativa del cierre de dependencias.

El registro de la presentación, [verification.txt](Grados26Learning/verification.txt),
corresponde al [pin histórico](https://github.com/wbgradost/ai-project/blob/7cc3a7406e09ba1544ff6997d5d742430c6c771c/paper/paper.pdf).
La declaración y la prueba que las diapositivas extraen de `Algebra.lean`
se conservan en las líneas 109–114.
