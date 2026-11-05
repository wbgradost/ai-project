"""Two-state extension; assistance is fixed during each CTMC experiment.

Rates are per model-time unit. Skill, effort and assistance share units.
Primitives are illustrative, not estimates.
"""
from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class Parameters:
    b: float = 2.0
    lambda0: float = 0.1
    kappa: float = 0.4
    mu: float = 0.3
    eta: float = 1.0

    def __post_init__(self):
        values = np.array([self.b, self.lambda0, self.kappa, self.mu, self.eta])
        if not np.all(np.isfinite(values)):
            raise ValueError("Parameters must be finite")
        if min(self.b, self.lambda0, self.kappa, self.mu) <= 0 or self.eta < 0:
            raise ValueError("Require b, lambda0, kappa, mu > 0 and eta >= 0")


def effort(a, p):
    a = np.asarray(a, dtype=float)
    if np.any(a < 0):
        raise ValueError("Assistance must be nonnegative")
    return np.maximum(p.b - a, 0.0)


def learning(a, p):
    return p.lambda0 + p.kappa * effort(a, p) * (1.0 + p.eta * np.asarray(a))


def share(a, p):
    lam = learning(a, p)
    return lam / (lam + p.mu)


def share_derivative(a, p):
    """Interior derivative only: the function has a kink at a=b."""
    a = np.asarray(a, dtype=float)
    if np.any((a < 0) | (a >= p.b)):
        raise ValueError("Derivative formula requires 0 <= a < b")
    return p.mu * p.kappa * (p.eta * (p.b - 2 * a) - 1) / (learning(a, p) + p.mu)**2


def thresholds(p):
    strong = p.eta * p.b > 1.0
    return {"peak": (p.b - 1.0 / p.eta) / 2 if strong else 0.0,
            "return": p.b - 1.0 / p.eta if strong else None,
            "effort_cutoff": p.b}


def transient_high(t, lam, mu, initial_high=0.0):
    pi = lam / (lam + mu)
    return pi + (initial_high - pi) * np.exp(-(lam + mu) * np.asarray(t))


def occupation_moments(T, lam, mu):
    """Exact moments of T^-1 integral_0^T 1{X_t=H} dt, starting L.

    E[Y^2] integrates P(X_s=H) P(X_t=H | X_s=H), s <= t.
    No independent-time-observation approximation is used.
    """
    T = np.asarray(T, dtype=float)
    r = lam + mu
    pi = lam / r
    d = -np.expm1(-r * T)
    mean = pi * (1.0 - d / (r * T))
    i1 = T**2 / 2 - T / r + d / r**2
    i2 = T * (1 + np.exp(-r * T)) - 2 * d / r
    second = 2 * pi * (pi * i1 + (1 - pi) * i2 / r) / T**2
    variance = second - mean**2
    if np.any(variance < -1e-12):
        raise ArithmeticError("Invalid occupation variance")
    return mean, np.maximum(variance, 0)


def simulate_occupation(lam, mu, horizons, rng):
    """Exact exponential holding times, starting L; integrate time in H.

    Jump counts converge to 1/2 in a two-state alternating chain, so they
    are deliberately not used as a stationary occupation estimator.
    """
    horizons = np.asarray(horizons, dtype=float)
    if lam <= 0 or mu <= 0 or np.any(horizons <= 0) or np.any(np.diff(horizons) <= 0):
        raise ValueError("Positive rates and increasing positive horizons required")
    end = horizons[-1]
    times, accumulated, states = [0.0], [0.0], [0]
    t, occupied, state = 0.0, 0.0, 0
    while t < end:
        next_t = min(t + rng.exponential(1.0 / (lam if state == 0 else mu)), end)
        occupied += state * (next_t - t)
        t = next_t
        times.append(t)
        accumulated.append(occupied)
        state = 1 - state
        states.append(state)
    index = np.searchsorted(times, horizons, side="right") - 1
    return (np.asarray(accumulated)[index]
            + np.asarray(states)[index] * (horizons - np.asarray(times)[index])) / horizons
