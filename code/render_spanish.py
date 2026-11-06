"""Redraw existing figures with Spanish labels, without rerunning simulations.

Run: python code/render_spanish.py
The original English PDFs and cached numerical outputs are left untouched.
The official single entry point, verify.py, also calls this renderer.
"""
import csv
from pathlib import Path

import verify as figures
import matplotlib.text


TRANSLATIONS = {
    "Human effort": "Esfuerzo humano",
    "Learning rate": "Tasa de aprendizaje",
    "Stationary high-skill share": "Proporción estacionaria\nde habilidad alta",
    "AI assistance, $a$": "Asistencia de IA, $a$",
    "peak\n0.5": "máximo\n0.5",
    "return 1": "retorno 1",
    "Marginal peak: $a^*/b$": "Máximo interior: $a^*/b$",
    "No-AI return: $a^R/b$": "Retorno sin IA: $a_R/b$",
    "Effort cutoff: $a/b=1$": "Esfuerzo nulo: $a/b=1$",
    "Locally increasing\nand above no AI": "Crecimiento local\ny mejora frente a no IA",
    "Decreasing, but\nabove no AI": "Disminuye, pero\nsupera el nivel sin IA",
    "Below no AI": "Inferior al nivel sin IA",
    "Zero effort: constant share": "Esfuerzo nulo:\nproporción constante",
    "Complementarity times initial effort, $\\eta b$": "Complementariedad × esfuerzo inicial, $\\eta b$",
    "Normalized assistance, $a/b$": "Asistencia normalizada, $a/b$",
    "Baseline learning, $\\lambda_0$": "Aprendizaje basal, $\\lambda_0$",
    "Learning from effort, $\\kappa$": "Aprendizaje por esfuerzo, $\\kappa$",
    "Skill depreciation, $\\mu$": "Depreciación de habilidades, $\\mu$",
    "Initial effort gap, $b$": "Esfuerzo inicial, $b$",
    "Value": "Valor",
    "CTMC occupation vs stationary prediction": "Ocupación simulada y estacionariedad",
    "High-skill time share": "Proporción de tiempo en habilidad alta",
    "Convergence: strong regime, $a=0.5$": "Convergencia: régimen fuerte, $a=0.5$",
    "Observation horizon, $T$": "Horizonte de observación, $T$",
    "Error vs stationary share (pp)": "Error frente al nivel estacionario (pp)",
    "Monte Carlo mean and 95% interval": "Media Monte Carlo e intervalo del 95 %",
    "Exact initial-state bias": "Sesgo exacto por el estado inicial",
}


def translate(text):
    text = TRANSLATIONS.get(text, text)
    for old, new in [("None:", "Nula:"), ("Weak:", "Débil:"), ("Strong:", "Fuerte:")]:
        if text.startswith(old):
            return new + text[len(old):]
    return text


def render_spanish(mc=None):
    if mc is None:
        with (figures.OUT / "ctmc_summary.csv").open(newline="", encoding="utf-8") as source:
            mc = [{key: value if key == "scenario" else float(value)
                   for key, value in row.items()} for row in csv.DictReader(source)]
    destination = Path(__file__).resolve().parent / "figures" / "es"
    destination.mkdir(parents=True, exist_ok=True)
    names = {"mechanism", "thresholds", "rate_sensitivity", "ctmc"}
    original_save = figures.save

    def save_spanish(fig, name):
        if name in names:
            for label in fig.findobj(match=matplotlib.text.Text):
                label.set_text(translate(label.get_text()))
            fig.savefig(destination / (name + ".pdf"),
                        metadata={"CreationDate": None, "ModDate": None})
        figures.plt.close(fig)

    try:
        figures.save = save_spanish
        figures.make_figures(mc)
    finally:
        figures.save = original_save


if __name__ == "__main__":
    render_spanish()
    print("Gráficos en español: code/figures/es/{mechanism,thresholds,rate_sensitivity,ctmc}.pdf")
