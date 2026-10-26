"""Recreate the numerical-evidence plot from held-out summaries.

This plot is not evidence of a minimax theorem. Confidence bars are descriptive
bootstrap intervals. Offline costs and information loss are disclosed below.
"""
from pathlib import Path
import json
import numpy as np
import matplotlib.pyplot as plt

root = Path(__file__).resolve().parents[1]
rows = json.loads((root / 'results/benchmark_summary.json').read_text())
labels = {
    'gha_reference': 'Giles–Haji-Ali: published constants',
    'gha_tuned': 'Giles–Haji-Ali: tuned',
    'v4_reference': 'v4: proved reference via Bernoulli conversion',
    'v4_tuned': 'v4: tuned via Bernoulli conversion',
}
fig, ax = plt.subplots(figsize=(9.5, 6))
for method, label in labels.items():
    selected = sorted((r for r in rows if r['method'] == method), key=lambda r: r['budget'])
    x = np.array([r['mean_work'] for r in selected])
    y = np.array([r['rmse'] for r in selected])
    lower = y - np.array([r['rmse_ci_low'] for r in selected])
    upper = np.array([r['rmse_ci_high'] for r in selected]) - y
    ax.errorbar(x, y, yerr=[lower, upper], marker='o', capsize=3, label=label)
ax.axhline(.025, linestyle='--', label='Constant zero: RMS error 0.025')
ax.axhline(.475, linestyle=':', label='Constant 1/2: RMS error 0.475')
ax.set_xscale('log'); ax.set_yscale('log')
ax.set_xlabel('Mean observed work (original inner-simulator draws)')
ax.set_ylabel('Held-out RMS error after clipping to [0, 1]')
ax.set_title('Giles–Haji-Ali model: practical comparison')
ax.legend(fontsize=8, loc='best'); ax.grid(True, which='major', alpha=.25)
fig.text(.5, .015,
    '500 replicates per cell; 150 at the largest budget. Bars: descriptive 95% bootstrap intervals.\n'
    'Offline training/tuning excluded from per-estimate work and reported separately. The conversion discards information.',
    ha='center', fontsize=8)
fig.tight_layout(rect=[0, .075, 1, 1])
fig.savefig(root/'report/benchmark_rmse.png', dpi=180)
fig.savefig(root/'report/benchmark_rmse.pdf')
plt.close(fig)
