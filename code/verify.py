"""Single entry point: check algebra, check claims, simulate exact CTMCs, plot.

Run from any directory: python code/verify.py
All outputs are recreated under code/output and code/figures. No data downloads.
Formula evaluations illustrate comparative statics; independent exact CTMC
trajectories check the stochastic implementation. Neither supplies a proof.
"""
from dataclasses import replace
from fractions import Fraction
import csv
import json
import os
import platform
from pathlib import Path

os.environ.setdefault("MPLCONFIGDIR",str(Path(__file__).resolve().parent/"__pycache__"/"matplotlib"))
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.ticker import NullLocator
import numpy as np
import sympy as sp

from model import (Parameters, effort, learning, share, share_derivative,
                   thresholds, transient_high, occupation_moments, simulate_occupation)

HERE = Path(__file__).resolve().parent
OUT, FIG = HERE / "output", HERE / "figures"
SEED = 20261104
REPLICATIONS = 384
HORIZONS = np.array([25.0, 100.0, 400.0])
MC_GATE = 6
DEMO_A, DEMO_GAMMA, DEMO_SKILL_L, DEMO_SKILL_H = 4., 1., 1., 3.
DEMO_TARGET = DEMO_A / DEMO_GAMMA - 1
BASE = Parameters(b=DEMO_TARGET - DEMO_SKILL_L)
SCENARIOS = [("None", 0.0), ("Weak", 0.25), ("Strong", 1.0)]
COLORS = ["#6b7280", "#d87812", "#1569a0"]
ASSISTANCE = np.array([0.0, 0.25, 0.5, 1.0, 1.5, 2.0, 2.5])
CRITICAL_PAIR = (0.4, 0.8)


def close(actual, expected, tol=1e-10, message="Numerical identity failed"):
    if not np.allclose(actual, expected, atol=tol, rtol=tol):
        raise AssertionError(f"{message}: {actual} versus {expected}")


def write_csv(name, rows):
    with (OUT / name).open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def symbolic_checks():
    a, b, eta, k, l0, mu = sp.symbols("a b eta k l0 mu", positive=True)
    lo, hi = sp.symbols("lo hi", nonnegative=True)
    lam = l0 + k * (b - a) * (1 + eta * a)
    pi = lam / (lam + mu)
    n = eta * (b - 2 * a) - 1
    identities = [
        sp.diff(lam, a) - k * n,
        sp.diff(lam, a) - (k * eta * (b - a) - k * (1 + eta * a)),
        sp.diff(pi, a) - mu * k * n / (lam + mu)**2,
        sp.diff(pi, a, 2) + 2 * mu * k *
        (eta * (lam + mu) + k * n**2) / (lam + mu)**3,
        lam - lam.subs(a, 0) - k * a * (eta * (b - a) - 1),
        lam.subs(a, hi) - lam.subs(a, lo)
        - k * (hi - lo) * (eta * (b - hi - lo) - 1),
        pi.subs(a, hi) - pi.subs(a, lo)
        - mu * (lam.subs(a, hi) - lam.subs(a, lo)) /
        ((lam.subs(a, hi) + mu) * (lam.subs(a, lo) + mu)),
        lam.subs(a, (b - 1 / eta) / 2) - l0 - k * (1 + eta * b)**2 / (4 * eta),
        sp.diff(pi, eta) - mu * k * a * (b - a) / (lam + mu)**2,
        sp.diff(pi, k) - mu * (b - a) * (1 + eta * a) / (lam + mu)**2,
        sp.diff(pi, l0) - mu / (lam + mu)**2,
        sp.diff(pi, mu) + lam / (lam + mu)**2,
        sp.diff(pi, b) - mu * k * (1 + eta * a) / (lam + mu)**2,
    ]
    # Gain relative to no AI: level effects need not imply monotone gains.
    factor=sp.symbols("factor",positive=True)
    C1,C0=l0+k*factor,l0+k*b
    M=(C1+mu)*(C0+mu);B=l0+mu
    G=mu*k*(factor-b)/M
    peak=(b-1/eta)/2;ret=b-1/eta
    peak_excess = (eta * b - 1)**2 / (4 * eta)
    baseline_denominator = l0 + k * b + mu
    normalized_peak_gain = mu * k / (
        4 * eta * baseline_denominator * (baseline_denominator + k * peak_excess)
    )
    A,gamma,skill=sp.symbols("A gamma skill",positive=True)
    gap=A/gamma-1-skill
    identities.extend([
        sp.diff(G,l0)+mu*k*(factor-b)*((C1+mu)+(C0+mu))/M**2,
        sp.diff(G,mu)-k*(factor-b)*(C1*C0-mu**2)/M**2,
        sp.diff(G,k)-mu*(factor-b)*(B**2-k**2*factor*b)/M**2,
        sp.diff(peak,eta)-1/(2*eta**2),sp.diff(peak,b)-sp.Rational(1,2),
        sp.diff(ret,eta)-1/eta**2,sp.diff(ret,b)-1,
        sp.diff(gap,A)-1/gamma,sp.diff(gap,gamma)+A/gamma**2,
        sp.diff(gap,skill)+1,
        ((b - peak) * (1 + eta * peak) - b) - (eta * b - 1)**2 / (4 * eta),
        sp.diff(1 / b, b) + 1 / b**2,
        sp.limit(peak, eta, 1 / b, dir="+"),
        sp.limit(ret, eta, 1 / b, dir="+"),
        sp.limit(peak, eta, sp.oo) - b / 2,
        sp.limit(ret, eta, sp.oo) - b,
        sp.limit(normalized_peak_gain, eta, 1 / b, dir="+")
        - mu * k * b / (4 * baseline_denominator**2),
    ])
    for i, expression in enumerate(identities):
        if sp.simplify(expression) != 0:
            raise AssertionError(f"Symbolic identity {i + 1} failed")
    # Stationary flow and forward equation; independent symbolic derivations.
    l, m, T = sp.symbols("l m T", positive=True)
    t, q = sp.symbols("t q", nonnegative=True)
    high = sp.Symbol("high")
    stationary = sp.solve([-(1-high)*l+high*m], high)
    if sp.simplify(stationary[high]-l/(l+m)) != 0:
        raise AssertionError("Stationary solution failed")
    r, ph = l + m, l / (l + m)
    decay = sp.exp(-r * t)
    generator = sp.Matrix([[-l, l], [m, -m]])
    transition = sp.Matrix([
        [1 - ph + ph * decay, ph * (1 - decay)],
        [(1 - ph) * (1 - decay), ph + (1 - ph) * decay],
    ])
    h = ph + (q - ph) * decay
    dynamics = [
        transition.diff(t) - transition * generator,
        transition.subs(t, 0) - sp.eye(2),
        transition * sp.ones(2, 1) - sp.ones(2, 1),
        sp.Matrix([[1 - q, q]]) * transition - sp.Matrix([[1 - h, h]]),
    ]
    for residual in dynamics:
        if residual.applyfunc(sp.simplify) != sp.zeros(*residual.shape):
            raise AssertionError("Transition law contradicts the generator, normalization, or initial law")
    occupation_mean = sp.integrate(h, (t, 0, T)) / T
    occupation_target = ph + (q - ph) * (1 - sp.exp(-r * T)) / (r * T)
    if sp.simplify(occupation_mean - occupation_target) != 0:
        raise AssertionError("Occupation mean for an arbitrary initial law failed")
    # Exact occupation second moment from the Markov joint law.
    s = sp.symbols("s", nonnegative=True)
    integrand = ph*(1-sp.exp(-r*s))*(ph*(T-s)+(1-ph)*(1-sp.exp(-r*(T-s)))/r)
    second = 2*sp.integrate(integrand,(s,0,T))/T**2
    i1 = T**2/2-T/r+(1-sp.exp(-r*T))/r**2
    i2 = T*(1+sp.exp(-r*T))-2*(1-sp.exp(-r*T))/r
    if sp.simplify(second-2*ph*(ph*i1+(1-ph)*i2/r)/T**2) != 0:
        raise AssertionError("Occupation second moment failed")
    A, gamma, skill, e = sp.symbols("A gamma skill e", positive=True)
    objective = A*sp.log(1+skill+e+a)-gamma*e
    root = A/gamma-1-skill-a
    if sp.simplify(sp.diff(objective,e).subs(e,root)) != 0:
        raise AssertionError("Worker FOC failed")
    corner_slope = gamma * root / (1 + skill + a)
    if sp.simplify(sp.diff(objective, e).subs(e, 0) - corner_slope) != 0:
        raise AssertionError("Worker corner condition failed")
    return len(identities) + len(dynamics) + 5


def check_worker_ties():
    # This C1 concave production function minus x is flat on [1, 3].
    # Dyadic grid points give exact equal payoff comparisons on the plateau.
    grid = np.arange(641) / 128
    inputs = [0, 0.5, 1, 2, 3, 3.25, 4]
    for z in inputs:
        x = z + grid
        production = np.piecewise(x, [x < 1, (x >= 1) & (x <= 3), x > 3],
                                  [lambda x: 2*x - x*x/2, lambda x: x + 0.5,
                                   lambda x: 3.5 + np.log(x - 2)])
        payoff = production - grid
        maximizers = grid[payoff == payoff.max()]
        close(maximizers[0], max(1-z, 0), message="First tied effort")
        close(maximizers[-1], max(3-z, 0), message="Largest selected effort")
    return len(inputs)


def check_pairwise_orders():
    skills = np.array([1., 3.])
    support_points = np.array([0., 1., 2., 3.])
    at_or_below = skills[:, None] <= support_points
    cases = [(0., .25, 1), (.25, .75, 0), (.5, .75, -1),
             (.75, 2., -1), (.75, 2.5, -1), (2., 2.5, 0)]
    for u, v, sign in cases:
        high_u, high_v = share(u, BASE), share(v, BASE)
        measure_u = np.array([1-high_u, high_u])
        measure_v = np.array([1-high_v, high_v])
        cdf_change = (measure_v - measure_u) @ at_or_below
        mean_change = (measure_v - measure_u) @ skills
        if sign == 0:
            close(cdf_change, np.zeros(len(support_points)), message="Equal skill distributions")
            close(mean_change, 0, message="Equal mean skills")
        elif (np.any(sign * cdf_change > 1e-10)
              or not np.any(sign * cdf_change < -1e-10)
              or sign * mean_change <= 0):
            raise AssertionError(f"Skill order failed at assistance {u}, {v}")
    return len(cases)


def check_gain_turning_points():
    a = thresholds(BASE)["peak"]
    f_a = effort(a, BASE) * (1 + BASE.eta*a)
    mu_peak = np.sqrt(learning(a, BASE) * learning(0, BASE))
    kappa_peak = (BASE.lambda0 + BASE.mu) / np.sqrt(f_a * BASE.b)
    for field, peak in [("mu", mu_peak), ("kappa", kappa_peak)]:
        def gain(value):
            params = replace(BASE, **{field: value})
            return share(a, params) - share(0, params)

        if gain(peak) <= max(gain(peak/2), gain(2*peak)):
            raise AssertionError(f"Gain must peak at the interior {field} threshold")
        step = 1e-5 * peak
        close((gain(peak+step)-gain(peak-step))/(2*step), 0, tol=1e-8,
              message=f"Gain derivative at the {field} threshold")


def deterministic_checks():
    rows, step = [], 0.00005
    grid = np.arange(0.0,7.0+step/2,step)
    # Independent maximization includes roots, corners, and both skill states.
    for A, gamma, s in [(DEMO_A, DEMO_GAMMA, DEMO_SKILL_L),
                        (DEMO_A, DEMO_GAMMA, DEMO_SKILL_H),
                        (3.1, .83, .5), (2., 1.5, 1.)]:
        for a in [0.,.13,.5,1.,1.93,2.,2.5,4.]:
            candidate=max(A/gamma-1-s-a,0)
            maximizer=grid[np.argmax(A*np.log1p(s+grid+a)-gamma*grid)]
            if abs(maximizer-candidate)>step:
                raise AssertionError("Effort formula disagrees with independent grid search")
            slope = A / (1 + s + a + candidate) - gamma
            if candidate > 0:
                close(slope, 0., message="Positive effort violates the worker FOC")
            elif slope > 1e-12:
                raise AssertionError("Zero effort violates the worker corner condition")
            rows.append(dict(A=A,gamma=gamma,skill=s,assistance=a,
                             effort_formula=candidate,effort_grid=maximizer,
                             absolute_error=abs(maximizer-candidate)))
    write_csv("effort_check.csv",rows)
    tie_cases = check_worker_ties()
    rng=np.random.default_rng(86021)  # Separate from CTMC streams.
    checked=0
    for j in range(300):
        p=Parameters(b=rng.uniform(.2,4),lambda0=rng.uniform(.01,1),
                     kappa=rng.uniform(.02,1.5),mu=rng.uniform(.02,1.5),
                     eta=0. if j%10==0 else rng.uniform(.01,5))
        a=rng.uniform(.02,.98)*p.b; h=1e-5*p.b
        close((share(a+h,p)-share(a-h,p))/(2*h),share_derivative(a,p),
              tol=2e-8,message="Derivative finite-difference check")
        lam=float(learning(a,p)); pi=float(share(a,p))
        Q=np.array([[-lam,lam],[p.mu,-p.mu]])
        if not (lam >= p.lambda0 > 0 and p.mu > 0 and 0 < pi < 1):
            raise AssertionError("Positive transition rates and interior stationarity required")
        close(np.array([1-pi,pi])@Q,np.zeros(2))
        close(Q@np.ones(2),np.zeros(2))
        # Independent numerical matrix exponential via uniformization.
        rate = max(lam, p.mu)
        jump = np.eye(2) + Q / rate
        count_mean = 0.35
        probability = np.exp(-count_mean)
        jump_power = np.eye(2)
        transition = probability * jump_power
        for count in range(1, 13):
            jump_power = jump_power @ jump
            probability *= count_mean / count
            transition += probability * jump_power
        time = count_mean / rate
        close(transition[:, 1], [transient_high(time, lam, p.mu, initial_high)
                                  for initial_high in (0., 1.)],
              message="Transition law versus uniformized generator")
        al,ah=sorted(rng.uniform(0,1,2)*p.b)
        predicted=p.mu*p.kappa*(ah-al)*(p.eta*(p.b-ah-al)-1)/((learning(ah,p)+p.mu)*(learning(al,p)+p.mu))
        close(share(ah,p)-share(al,p),predicted)
        close(share(p.b,p),p.lambda0/(p.lambda0+p.mu))
        close(share(p.b+1,p),share(p.b,p)); close(effort(p.b,p),0.)
        close(share(p.b,p)-share(al,p),
              p.mu*p.kappa*(p.b-al)*(p.eta*(p.b-p.b-al)-1)
              /((learning(p.b,p)+p.mu)*(learning(al,p)+p.mu)))
        if not share(p.b+.5,p)<share(al,p):
            raise AssertionError("Active-effort share must exceed zero-effort plateau")
        t=thresholds(p)
        for field in ["lambda0","kappa","mu"]:
            changed=replace(p,**{field:getattr(p,field)*2.7})
            if thresholds(changed)!=t:
                raise AssertionError("Rate parameter changed threshold location")
        scaled=replace(p,lambda0=3*p.lambda0,kappa=3*p.kappa,mu=3*p.mu)
        close(share(np.linspace(0,1.3*p.b,51),scaled),share(np.linspace(0,1.3*p.b,51),p))
        close(transient_high(.7,3*lam,3*p.mu),transient_high(2.1,lam,p.mu))
        if p.eta*p.b>1:
            close(t["return"],2*t["peak"])
            close(share(t["return"],p),share(0,p))
            close(share_derivative(t["peak"],p),0.)
            close(learning(t["peak"],p),p.lambda0+p.kappa*(1+p.eta*p.b)**2/(4*p.eta))
            if not (0<t["peak"]<t["return"]<p.b):
                raise AssertionError("Threshold ordering failed")
            dense=np.linspace(0,1.3*p.b,3001)
            if np.max(share(dense,p))>share(t["peak"],p)+1e-10:
                raise AssertionError("Claimed global maximum failed")
            if not share(t["return"]/2,p)>share(0,p):
                raise AssertionError("Strict baseline gain interval failed")
            if not share((t["return"]+p.b)/2,p)<share(0,p):
                raise AssertionError("Loss beyond return threshold failed")
        elif t["peak"] != 0 or t["return"] is not None:
            raise AssertionError("No or weak complementarity must maximize at zero")
        elif not np.all(np.diff(share(np.linspace(0, p.b, 101), p)) < 0):
            raise AssertionError("No or weak complementarity must strictly decline")
        checked+=1
    # Critical equality is not a reversal.
    critical=replace(BASE,eta=1/BASE.b)
    close(share_derivative(0,critical),0.)
    if not share(.01,critical)<share(0,critical):
        raise AssertionError("Critical boundary incorrectly labelled reversal")
    # The cutoff is a kink, not a smooth stationary point.
    for eta in [*(eta for _, eta in SCENARIOS), critical.eta]:
        p=replace(BASE,eta=eta); eps=1e-7
        expected=-p.mu*p.kappa*(1+p.eta*p.b)/(p.lambda0+p.mu)**2
        close((share(p.b,p)-share(p.b-eps,p))/eps,expected,tol=2e-6)
        close((share(p.b+eps,p)-share(p.b,p))/eps,0.)
        active_shares = share(np.linspace(0, p.b, 51), p)
        if not np.all(np.diff(active_shares, n=2) < 0):
            raise AssertionError("Stationary curve must be strictly concave on the active interval")
        if not share(p.b,p) < (share(0,p) + share(2*p.b,p))/2:
            raise AssertionError("Concavity must fail at the midpoint across the plateau boundary")
        # At fixed assistance a=b, varying b crosses from the plateau to active effort.
        left = replace(p, b=p.b - eps)
        right = replace(p, b=p.b + eps)
        close((share(p.b, p) - share(p.b, left)) / eps, 0.)
        close((share(p.b, right) - share(p.b, p)) / eps, -expected, tol=2e-6)
        raised_eta = replace(p, eta=p.eta + eps)
        raised_kappa = replace(p, kappa=p.kappa + eps)
        close(share([0., p.b, 1.5 * p.b], raised_eta), share([0., p.b, 1.5 * p.b], p))
        close(share([p.b, 1.5 * p.b], raised_kappa), share([p.b, 1.5 * p.b], p))
        if not share(p.b / 2, raised_eta) > share(p.b / 2, p):
            raise AssertionError("Positive active assistance must benefit from greater complementarity")
        if not share(p.b / 2, raised_kappa) > share(p.b / 2, p):
            raise AssertionError("Active effort must benefit from greater effort sensitivity")
    # Hand-critical comparison: both beat no AI, but the higher AI level loses.
    u, v = CRITICAL_PAIR
    close(effort(u, BASE) * (1 + BASE.eta * u), 2.24)
    close(effort(v, BASE) * (1 + BASE.eta * v), 2.16)
    if not share(0, BASE) < share(v, BASE) < share(u, BASE):
        raise AssertionError("Pairwise counterexample failed")
    close(share(.5,BASE),10/13); close(share(0,BASE),3/4)
    close(share(.5,BASE)-share(0,BASE),1/52)
    close(effort(.5,BASE),1.5); close(learning(.5,BASE),1.)
    close(share(.2,BASE),share(.8,BASE))
    close(share(BASE.b, BASE), 1 / 4)
    close(learning(0., BASE), .9)
    pairwise_cases = check_pairwise_orders()
    check_gain_turning_points()
    return {"effort_grid_max_error":max(r["absolute_error"] for r in rows),
            "effort_grid_step":step,"random_parameter_cases":checked,
            "worker_tie_and_corner_cases":tie_cases,"skill_order_cases":pairwise_cases}


def comparative_data():
    rows=[]
    for label,eta in SCENARIOS:
        p=replace(BASE,eta=eta)
        for a in np.linspace(0,2.5,501):
            rows.append(dict(scenario=label,eta=eta,assistance=a,
                             effort=float(effort(a,p)),learning=float(learning(a,p)),
                             stationary_high=float(share(a,p))))
    write_csv("comparative_statics.csv",rows)
    sensitivity=[]
    for field,values in [("eta",[0.,.25,.5,1.,2.]),("kappa",[.1,.4,.8]),
                         ("lambda0",[.02,.1,.5]),("mu",[.1,.3,1.]),
                         ("b",[.75,1.,2.,3.])]:
        for value in values:
            p=replace(BASE,**{field:value}); t=thresholds(p)
            sensitivity.append(dict(parameter=field,value=value,b=p.b,eta=p.eta,
                                    peak=t["peak"],return_to_baseline=t["return"],
                                    effort_cutoff=t["effort_cutoff"],pi0=float(share(0,p)),
                                    pi_peak=float(share(t["peak"],p)),
                                    peak_gain_pp=100*float(share(t["peak"],p)-share(0,p))))
    write_csv("sensitivity.csv",sensitivity)
    scenarios=[]
    for name,eta in SCENARIOS:
        p=replace(BASE,eta=eta);t=thresholds(p)
        scenarios.append(dict(scenario=name,eta=eta,eta_b=eta*p.b,**t,
                              pi0=float(share(0,p)),pi_peak=float(share(t["peak"],p)),
                              pi_cutoff=float(share(p.b,p))))
    write_csv("scenarios.csv",scenarios)
    critical_pair = [
        dict(assistance=a, effort=float(effort(a, BASE)),
             effort_learning_factor=float(effort(a, BASE)) * (1 + BASE.eta * a),
             learning=float(learning(a, BASE)), stationary_high=float(share(a, BASE)))
        for a in (0., *CRITICAL_PAIR)
    ]
    write_csv("critical_pair.csv", critical_pair)
    return scenarios, critical_pair


def handwritten_check():
    """Check the photographed counterexample with its own exact inputs."""
    b, eta = Fraction(2), Fraction(1)
    lambda0, kappa, mu = Fraction(1, 4), Fraction(1), Fraction(3, 4)
    high_assistance = Fraction(3, 2)
    peak = (b - 1 / eta) / 2
    ret = 2 * peak
    doses = (Fraction(0), peak, high_assistance)
    efforts = [max(b - a, 0) for a in doses]
    rates = [lambda0 + kappa * effort_at_a * (1 + eta * a)
             for a, effort_at_a in zip(doses, efforts)]
    shares = [rate / (rate + mu) for rate in rates]
    if (not 0 < peak < ret < high_assistance < b
            or efforts[-1] != Fraction(1, 2)
            or rates != [Fraction(9, 4), Fraction(5, 2), Fraction(3, 2)]
            or shares != [Fraction(3, 4), Fraction(10, 13), Fraction(2, 3)]
            or not shares[-1] < shares[0] < shares[1]):
        raise AssertionError("The photographed counterexample failed")
    p = Parameters(b=float(b), lambda0=float(lambda0), kappa=float(kappa),
                   mu=float(mu), eta=float(eta))
    numeric_doses = list(map(float, doses))
    close(learning(numeric_doses, p), list(map(float, rates)))
    close(share(numeric_doses, p), list(map(float, shares)))
    return {
        "HandInitialEffort": b, "HandEta": eta, "HandLambdaZero": lambda0,
        "HandKappa": kappa, "HandMu": mu, "HandPeak": peak, "HandReturn": ret,
        "HandHighAssistance": high_assistance, "HandHighEffort": efforts[-1],
        "HandBaselineRate": rates[0], "HandPeakRate": rates[1], "HandHighRate": rates[2],
        "HandBaselineShare": shares[0], "HandPeakShare": shares[1], "HandHighShare": shares[2],
    }


def stochastic_checks():
    rows=[]
    # One child per cell, then a grandchild per independent trajectory.
    children=np.random.SeedSequence(SEED).spawn(len(SCENARIOS)*len(ASSISTANCE))
    for cell,(label,eta,a) in enumerate((label,eta,a) for label,eta in SCENARIOS for a in ASSISTANCE):
        p=replace(BASE,eta=eta);lam=float(learning(a,p));pi=float(share(a,p))
        repseeds=children[cell].spawn(REPLICATIONS)
        values=np.array([simulate_occupation(lam,p.mu,HORIZONS,np.random.default_rng(seed)) for seed in repseeds])
        if np.any(~np.isfinite(values) | (values < 0) | (values > 1)):
            raise AssertionError("Occupation estimate outside [0,1]")
        target,variance=occupation_moments(HORIZONS,lam,p.mu)
        means=values.mean(axis=0);sem=values.std(axis=0,ddof=1)/np.sqrt(REPLICATIONS)
        exact_se=np.sqrt(variance/REPLICATIONS)
        z=(means-target)/exact_se
        if not np.all(np.isfinite(z) & (np.abs(z) <= MC_GATE)):
            raise AssertionError(f"CTMC mean exceeds {MC_GATE} exact MC standard errors: {label}, a={a}, z={z}")
        for j,T in enumerate(HORIZONS):
            rows.append(dict(scenario=label,eta=eta,assistance=float(a),horizon=float(T),
                             replications=REPLICATIONS,lambda_L=lam,mu=p.mu,stationary=pi,
                             exact_occupation_mean=float(target[j]),initial_bias=float(target[j]-pi),
                             mc_mean=float(means[j]),mc_sem=float(sem[j]),
                             ci95_low=float(means[j]-1.96*sem[j]),ci95_high=float(means[j]+1.96*sem[j]),
                             exact_sem=float(exact_se[j]),z_exact=float(z[j]),
                             error_vs_stationary=float(means[j]-pi)))
    write_csv("ctmc_summary.csv",rows)
    final=[r for r in rows if r["horizon"]==HORIZONS[-1]]
    return rows,{"seed":SEED,"replications":REPLICATIONS,"initial_state":"L",
                 "burn_in":0,"horizons":HORIZONS.tolist(),"cells":len(final),
                 "max_abs_error_vs_stationary":max(abs(r["error_vs_stationary"]) for r in final),
                 "max_abs_error_vs_exact_finite_horizon_mean":max(abs(r["mc_mean"]-r["exact_occupation_mean"]) for r in final),
                 "max_abs_z_all_horizons":max(abs(r["z_exact"]) for r in rows),
                 "max_abs_initial_bias_final":max(abs(r["initial_bias"]) for r in final),
                 "max_empirical_sem_final":max(r["mc_sem"] for r in final),
                 "nominal_95_coverage_finite_horizon":sum(r["ci95_low"]<=r["exact_occupation_mean"]<=r["ci95_high"] for r in rows)/len(rows),
                 "validation_rule": f"abs(mean-exact finite-horizon mean) <= {MC_GATE} exact MC standard errors; diagnostic, not proof"}


def style_axis(ax):
    ax.spines[["top","right"]].set_visible(False)
    ax.grid(alpha=.13)


def save(fig,name):
    fig.savefig(FIG/(name+".pdf"),metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


def make_figures(mc):
    plt.rcParams.update({"font.size":11,"axes.titlesize":12,"axes.labelsize":11,
                         "legend.fontsize":9,"pdf.fonttype":42,"font.family":"DejaVu Sans"})
    a=np.linspace(0,2.5,501)
    strong_thresholds = thresholds(BASE)
    peak, ret = strong_thresholds["peak"], strong_thresholds["return"]
    fig,axes=plt.subplots(1,3,figsize=(11.6,3.7),constrained_layout=True)
    axes[0].plot(a,effort(a,BASE),color="#333333",lw=2.3)
    for (label,eta),color in zip(SCENARIOS,COLORS):
        p=replace(BASE,eta=eta)
        axes[1].plot(a,learning(a,p),color=color,lw=2.3,label=f"{label}: $\\eta={eta:g}$")
        axes[2].plot(a,share(a,p),color=color,lw=2.3)
    for ax,title,ylabel in zip(axes,["Human effort","Learning rate","Stationary high-skill share"],
                              ["$e_L^*(a)$","$\\lambda_L(a)$","$\\pi_H(a)$"]):
        style_axis(ax);ax.set(xlabel="AI assistance, $a$",ylabel=ylabel,title=title,xlim=(0,2.5))
        ax.axvline(BASE.b,color="black",ls=":",lw=1)
    axes[1].legend(loc="lower left",frameon=False)
    axes[2].axhline(share(0., BASE),color="black",lw=.8,ls="--")
    axes[2].axvline(peak,color=COLORS[2],ls="--",lw=.9)
    axes[2].axvline(ret,color=COLORS[2],ls=":",lw=1)
    axes[2].text(peak,.81,f"peak\n{peak:g}",ha="center",fontsize=9,color=COLORS[2])
    axes[2].text(ret+.1,.83,f"return {ret:g}",fontsize=9,color=COLORS[2])
    axes[2].set_ylim(.2,.9)
    save(fig,"mechanism")

    # z=eta*b and u=a/b display the shape invariance.
    z=np.linspace(0,5,601);u=np.linspace(0,1.2,401)
    zz,uu=np.meshgrid(z,u)
    region=np.zeros_like(zz,dtype=int)
    gain=(uu<1)&(uu>0)&(zz*(1-uu)>1)
    local=(uu<1)&(zz*(1-2*uu)>1)
    region[gain]=1;region[local]=2;region[uu>=1]=3
    fig,ax=plt.subplots(figsize=(7.5,4.5),constrained_layout=True)
    ax.pcolormesh(z,u,region,cmap=ListedColormap(["#f0e2d0","#a9c7dd","#3b8dbc","#dddddd"]),
                  shading="nearest",vmin=0,vmax=3,rasterized=True)
    zs=np.linspace(1.00001,5,500)
    ax.plot(zs,.5*(1-1/zs),color="#123b54",lw=2,label="Marginal peak: $a^*/b$")
    ax.plot(zs,1-1/zs,color="#123b54",ls="--",lw=2,label="No-AI return: $a_R/b$")
    ax.axhline(1,color="black",ls=":",label="Effort cutoff: $a/b=1$")
    ax.axvline(1,color="black",lw=.8,alpha=.5)
    ax.text(3.1,.17,"Locally increasing\nand above no AI",ha="center",color="white")
    ax.text(3.35,.56,"Decreasing, but\nabove no AI",ha="center",color="#16374e")
    ax.text(1.5,.88,"Below no AI",ha="center",color="#4e3823")
    ax.text(2.6,1.08,"Zero effort: constant share",ha="center")
    ax.set(xlabel="Complementarity times initial effort, $\\eta b$",ylabel="Normalized assistance, $a/b$",
           xlim=(0,5),ylim=(0,1.2))
    ax.legend(loc="upper left",frameon=False,fontsize=9,bbox_to_anchor=(0,1.01))
    save(fig,"thresholds")

    fig,axes=plt.subplots(2,2,figsize=(9.2,6.2),constrained_layout=True)
    settings=[("lambda0",[.02,.1,.5],"Baseline learning, $\\lambda_0$"),
              ("kappa",[.1,.4,.8],"Learning from effort, $\\kappa$"),
              ("mu",[.1,.3,1.],"Skill depreciation, $\\mu$"),
              ("b",[.75,1.,2.,3.],"Initial effort gap, $b$")]
    for ax,(field,values,title) in zip(axes.flat,settings):
        for value in values:
            p=replace(BASE,**{field:value})
            av=np.linspace(0,3.3 if field=="b" else 2.5,501)
            line,=ax.plot(av,share(av,p),lw=1.8,label=f"{value:g}")
            panel_peak=thresholds(p)["peak"]
            ax.plot(panel_peak,share(panel_peak,p),"o",ms=4,color=line.get_color())
        if field!="b":
            ax.axvline(peak,color="black",lw=.9,ls=":")
            ax.axvline(ret,color="black",lw=.9,ls="--",alpha=.5)
        style_axis(ax);ax.set(xlabel="AI assistance, $a$",ylabel="$\\pi_H(a)$",title=title)
        ax.legend(frameon=False,loc="best",title="Value",fontsize=9)
    save(fig,"sensitivity")

    # A wide rendering of the same three rate panels keeps slide labels legible.
    fig,axes=plt.subplots(1,3,figsize=(11.6,3.7),constrained_layout=True)
    for ax,(field,values,title) in zip(axes,settings[:3]):
        for value in values:
            p=replace(BASE,**{field:value})
            line,=ax.plot(a,share(a,p),lw=2,label=f"{value:g}")
            ax.plot(peak,share(peak,p),"o",ms=4,color=line.get_color())
        ax.axvline(peak,color="black",lw=.9,ls=":")
        ax.axvline(ret,color="black",lw=.9,ls="--",alpha=.5)
        style_axis(ax)
        ax.set(xlabel="AI assistance, $a$",ylabel="$\\pi_H(a)$",title=title)
        ax.legend(frameon=False,loc="best",title="Value",fontsize=9)
    save(fig,"rate_sensitivity")

    fig,axes=plt.subplots(1,2,figsize=(10,4.1),constrained_layout=True)
    for (label,eta),color in zip(SCENARIOS,COLORS):
        p=replace(BASE,eta=eta)
        group=[r for r in mc if r["scenario"]==label and r["horizon"]==HORIZONS[-1]]
        axes[0].plot(a,share(a,p),color=color,lw=1.7,label=f"{label}: $\\eta={eta:g}$")
        axes[0].errorbar([r["assistance"] for r in group],[r["mc_mean"] for r in group],
                         yerr=[1.96*r["mc_sem"] for r in group],fmt="o",ms=4,capsize=3,color=color)
    axes[0].set(xlabel="AI assistance, $a$",ylabel="High-skill time share",title="CTMC occupation vs stationary prediction")
    axes[0].legend(frameon=False,fontsize=9)
    group=[r for r in mc if r["eta"]==BASE.eta and r["assistance"]==peak]
    axes[1].errorbar([r["horizon"] for r in group],[100*r["error_vs_stationary"] for r in group],
                     yerr=[100*1.96*r["mc_sem"] for r in group],fmt="o",capsize=4,color=COLORS[2],
                     label="Monte Carlo mean and 95% interval")
    Ts=np.geomspace(20,450,300)
    lam=float(learning(peak,BASE));target,_=occupation_moments(Ts,lam,BASE.mu)
    axes[1].plot(Ts,100*(target-share(peak,BASE)),color="black",ls="--",label="Exact initial-state bias")
    axes[1].axhline(0,color="black",lw=.8)
    axes[1].set(xscale="log",xlabel="Observation horizon, $T$",ylabel="Error vs stationary share (pp)",
                title=f"Convergence: strong regime, $a={peak:g}$")
    axes[1].set_xticks(HORIZONS,labels=[f"{horizon:g}" for horizon in HORIZONS])
    axes[1].xaxis.set_minor_locator(NullLocator())
    axes[1].legend(frameon=False,fontsize=8,loc="lower right")
    for ax in axes:style_axis(ax)
    save(fig,"ctmc")


def write_tex(scenarios, critical_pair, hand_values, mc, metrics):
    p=BASE;t=thresholds(p)
    macros={"PeakAssistance":t["peak"],"ReturnAssistance":t["return"],
            "EffortCutoff":p.b,"BaselineShare":share(0,p),"PeakShare":share(t["peak"],p),
            "PeakGainPP":100*(share(t["peak"],p)-share(0,p)),"CutoffShare":share(p.b,p),
            "MCReplications":REPLICATIONS,"MCHorizon":int(HORIZONS[-1]),"MCSeed":SEED,
            "MCMaxAbsError":metrics["max_abs_error_vs_stationary"],
            "MCMaxAbsErrorPP":100*metrics["max_abs_error_vs_stationary"],
            "MCMaxFiniteErrorPP":100*metrics["max_abs_error_vs_exact_finite_horizon_mean"],
            "MCMaxBiasPP":100*metrics["max_abs_initial_bias_final"],
            "MCMaxZ":metrics["max_abs_z_all_horizons"],
            "MCMaxSE":metrics["max_empirical_sem_final"],
            "MCCoveragePct":100*metrics["nominal_95_coverage_finite_horizon"]}
    paper_values = {
        "DemoA": f"{DEMO_A:g}", "DemoGamma": f"{DEMO_GAMMA:g}",
        "DemoSkillL": f"{DEMO_SKILL_L:g}", "DemoSkillH": f"{DEMO_SKILL_H:g}",
        "DemoTarget": f"{DEMO_TARGET:g}", "DemoInitialEffort": f"{p.b:g}",
        "DemoLambdaZero": f"{p.lambda0:g}", "DemoKappa": f"{p.kappa:g}",
        "DemoMu": f"{p.mu:g}", "DemoCriticalEta": f"{1 / p.b:g}",
        "DemoEtaGrid": ",".join(f"{r['eta']:g}" for r in scenarios),
        "DemoEtaBGrid": ",".join(f"{r['eta_b']:g}" for r in scenarios),
        "DemoPeak": f"{t['peak']:g}", "DemoReturn": f"{t['return']:g}",
        "DemoBaselineLearning": f"{learning(0., p):g}",
        "DemoPeakLearning": f"{learning(t['peak'], p):g}",
        "DemoBaselineEffortFactor": f"{effort(0., p):g}",
        "DemoPeakEffortFactor": f"{effort(t['peak'], p) * (1 + p.eta * t['peak']):g}",
        "MCCells": str(metrics["cells"]), "MCGate": str(MC_GATE),
        "MCHorizons": ",".join(f"{horizon:g}" for horizon in HORIZONS),
        "MCAssistanceGrid": ",".join(f"{a:g}" for a in ASSISTANCE),
    }
    # Preserve the exact rational arithmetic of the illustrative inputs.
    b, eta, lambda0, kappa, mu = map(
        Fraction, map(str, (p.b, p.eta, p.lambda0, p.kappa, p.mu))
    )
    peak = (b - 1 / eta) / 2
    baseline_rate = lambda0 + kappa * b
    peak_rate = lambda0 + kappa * (b - peak) * (1 + eta * peak)
    baseline_share = baseline_rate / (baseline_rate + mu)
    peak_share = peak_rate / (peak_rate + mu)
    cutoff_share = lambda0 / (lambda0 + mu)
    peak_gain = peak_share - baseline_share
    close([float(peak), float(baseline_share), float(peak_share), float(cutoff_share),
           float(peak_gain)],
          [t["peak"], share(0., p), share(t["peak"], p), share(p.b, p),
           share(t["peak"], p) - share(0., p)],
          message="Exact illustrative fractions disagree with the numerical model")
    exact_values = {
        "DemoBaselineShareExact": baseline_share, "DemoPeakShareExact": peak_share,
        "DemoCutoffShareExact": cutoff_share, "DemoPeakGainExact": peak_gain,
        **hand_values,
    }
    for key, value in exact_values.items():
        paper_values[key] = (str(value) if value.denominator == 1 else
                             rf"\frac{{{value.numerator}}}{{{value.denominator}}}")
    for label, row in zip(("Low", "High"), critical_pair[1:]):
        paper_values[f"DemoPair{label}Assistance"] = f"{row['assistance']:g}"
        paper_values[f"DemoPair{label}Share"] = f"{row['stationary_high']:.4f}"
    with (OUT/"results.tex").open("w",encoding="utf-8") as f:
        f.write("% Generated by code/verify.py; do not edit.\n")
        for key,value in macros.items():
            formatted=str(value) if isinstance(value,int) else f"{float(value):.4f}"
            f.write("\\newcommand{\\"+key+"}{"+formatted+"}\n")
        for key, value in paper_values.items():
            f.write(f"\\newcommand{{\\{key}}}{{{value}}}\n")
    with (OUT/"scenarios_table.tex").open("w",encoding="utf-8") as f:
        f.write("% Table body: scenario, eta, eta*b, peak, return, pi0, pi_peak.\n")
        for r in scenarios:
            ret="---" if r["return"] is None else f'{r["return"]:.2f}'
            f.write(f'{r["scenario"]} & {r["eta"]:.2f} & {r["eta_b"]:.2f} & {r["peak"]:.2f} & {ret} & {r["pi0"]:.4f} & {r["pi_peak"]:.4f} '+r'\\'+"\n")
    with (OUT/"ctmc_table.tex").open("w",encoding="utf-8") as f:
        f.write("% Table body: scenario, assistance, stationary, MC mean, SEM, initial bias.\n")
        for r in mc:
            if r["horizon"]==HORIZONS[-1] and r["assistance"] in [0.,.5,1.,2.]:
                f.write(f'{r["scenario"]} & {r["assistance"]:.1f} & {r["stationary"]:.4f} & {r["mc_mean"]:.4f} & {r["mc_sem"]:.4f} & {r["initial_bias"]:.4f} '+r'\\'+"\n")


def main():
    OUT.mkdir(exist_ok=True);FIG.mkdir(exist_ok=True)
    count=symbolic_checks()
    checks=deterministic_checks()
    scenarios, critical_pair = comparative_data()
    hand_values = handwritten_check()
    checks["handwritten_counterexample"] = {
        "assistance": str(hand_values["HandHighAssistance"]),
        "no_ai_share": str(hand_values["HandBaselineShare"]),
        "assisted_share": str(hand_values["HandHighShare"]),
    }
    mc,metrics=stochastic_checks()
    make_figures(mc)
    write_tex(scenarios, critical_pair, hand_values, mc, metrics)
    summary={"runtime":{"python":platform.python_version(),"numpy":np.__version__,
                        "sympy":sp.__version__,"matplotlib":matplotlib.__version__},
             "parameters":{"A":int(DEMO_A),"gamma":int(DEMO_GAMMA),
                           "s_L":int(DEMO_SKILL_L),"s_H":int(DEMO_SKILL_H),"x_star":int(DEMO_TARGET),
                           "b":BASE.b,"lambda0":BASE.lambda0,"kappa":BASE.kappa,"mu":BASE.mu},
             "scenarios":scenarios,"symbolic_identities":count,"deterministic_checks":checks,
             "ctmc":metrics,"interpretation":"Illustrative parameters, not estimated; no welfare or N-state claim."}
    (OUT/"summary.json").write_text(json.dumps(summary,indent=2)+"\n",encoding="utf-8")
    from render_spanish import render_spanish
    render_spanish(mc=mc)
    print(f"PASS: {count} symbolic checks; {checks['random_parameter_cases']} random parameter cases; independent effort grid check.")
    print(f"PASS: {checks['worker_tie_and_corner_cases']} worker tie and corner cases, "
          f"{checks['skill_order_cases']} distributional comparisons, and gain turning points.")
    print("PASS: exact rational check of the photographed counterexample.")
    t = thresholds(BASE)
    print(f"Strong complementarity: peak a={t['peak']:g}, no-AI return a={t['return']:g}, zero effort a={BASE.b:g}.")
    print(f"High-skill share: no AI={share(0,BASE):.6f}; peak={share(t['peak'],BASE):.6f}; zero-effort plateau={share(BASE.b,BASE):.6f}.")
    print(f"CTMC: {metrics['cells']} parameter cells, {REPLICATIONS} independent paths per cell; seed={SEED}; T={HORIZONS.tolist()}.")
    print(f"T=400 maximum absolute error vs stationary={100*metrics['max_abs_error_vs_stationary']:.4f} pp; maximum exact initial-state bias={100*metrics['max_abs_initial_bias_final']:.4f} pp.")
    print(f"Maximum standardized error vs exact finite-horizon mean={metrics['max_abs_z_all_horizons']:.3f} (pass threshold {MC_GATE}).")
    print("PASS: generated manuscript and slide figures, CSV data, LaTeX numbers and tables, and summary.json.")


if __name__=="__main__":
    main()
