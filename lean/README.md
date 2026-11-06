# Grados26Learning: evidencia formal utilizada en la presentación

El manuscrito permanece fijado en
[`7cc3a7406e09ba1544ff6997d5d742430c6c771c`](https://github.com/wbgradost/ai-project/blob/7cc3a7406e09ba1544ff6997d5d742430c6c771c/paper/paper.pdf).
No se modifican sus proposiciones numeradas.

`Grados26Learning/Model.lean` y `Algebra.lean` son copias fieles del trabajo
existente en `papers/Grados26Learning/` de AppliedModelingLib, worktree
`/home/william/AppliedModelingLib-Grados26Learning` (base de la biblioteca:
`194edcc95df74806a39b961d10dedddc6e730cce`). Se conservan los módulos
compilados necesarios para la evidencia de la presentación, sin presentar los
borradores restantes como demostraciones verificadas.

La declaración mostrada es `Grados26Learning.active_pair_increase_iff`, en
`Algebra.lean`, líneas 109–114. Prueba exactamente la comparación de la
Proposición 2 para 0 ≤ u < v ≤ b: mayor asistencia mejora la fórmula estacionaria
si y solo si eta · (b − u − v) > 1. `Parameters` contiene exclusivamente las
positividades originales y eta ≥ 0. No hay hipótesis económica adicional.
El módulo también demuestra las comparaciones de igualdad y disminución,
la saturación y la equivalencia del orden de proporciones con dominancia
estocástica y habilidad media en dos estados.

`PresentationCheck.lean` importa ese módulo ya compilado y consulta las
declaraciones y los axiomas del teorema mostrado. `verification.txt` conserva
la salida auténtica de esta comprobación estrecha, la versión de Lean y las
huellas de los dos archivos originales. Los axiomas fundacionales estándar de
Lean/Mathlib no constituyen supuestos económicos añadidos. No se utiliza
`sorry`, `admit` ni un axioma adicional para obtener la conclusión.

Desde el mismo entorno AppliedModelingLib, con estos módulos disponibles:

```bash
lake env lean /ruta/a/ai-project/lean/Grados26Learning/PresentationCheck.lean
```

Esta comprobación no es el paper-scoped check oficial ni una certificación
completa de los cinco resultados. En particular, aquí no se da por formalizada
la construcción probabilística de la cadena, el optimizador original, la
caracterización global completa ni todo el corolario de sensibilidad. La
presentación distingue estas limitaciones de las demostraciones analíticas
existentes. Completar el procedimiento oficial del paper sigue requiriendo
cerrar esos componentes, ejecutar
`python3 scripts/paper_contribution.py check Grados26Learning --fast` y trasladar
la carpeta generada completa respetando su `.gitignore`, como exige el
[Issue #7](https://github.com/alexanderquispe/AI-Econ-Modeling/issues/7).
