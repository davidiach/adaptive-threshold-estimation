"""Kernel certificates for zero-residual envelopes and law rounding/transfer.

Transfer validity is conditional on the stated law and input-K enclosure
premises. Envelope fallback outputs are tagged placeholders, not integrals.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
import hashlib
from pathlib import Path
import subprocess
from types import SimpleNamespace
from typing import Any

from . import deterministic_certificates as dc
from . import finite_law_certificates as fc
from .gap_envelope import GapEnvelope
from .rare_event_functional import (FiniteGapLaw, Interval, Precision, band_index,
                                   quantile_split, round_up_within_bands, transfer_enclosure)

VerificationError = dc.VerificationError
SCHEMA = "ate-kernel-envelope-transfer-v1"


def _integer(x, lo, hi, name):
    if type(x) is not int or not lo <= x <= hi:
        raise VerificationError(f"{name} must be an integer in [{lo},{hi}].")


@dataclass(frozen=True)
class EnvelopeRequest:
    cdf: tuple[F, ...]
    rho: F = F(1, 4)
    budget: F = F(256)
    cap: int = 1024
    heads: int = 0
    tails: int = 0
    bits: int = 80
    log_terms: int = 32

    def __post_init__(self):
        if type(self.cdf) is not tuple or not 1 <= len(self.cdf) <= 17:
            raise VerificationError("Supply 1 to 17 exact CDF bounds in a tuple.")
        values = tuple(dc._exact(x) for x in self.cdf)
        if values[0] != 1 or any(not 0 <= x <= 1 for x in values) or any(a < b for a, b in zip(values, values[1:])):
            raise VerificationError("CDF bounds must start at one, lie in [0,1], and decrease.")
        object.__setattr__(self, "cdf", values)
        for k in ("rho", "budget"):
            object.__setattr__(self, k, dc._exact(getattr(self, k)))
        if not 0 < self.rho <= F(1, 4) or self.budget <= 0:
            raise VerificationError("Require 0 < rho <= 1/4 and positive budget.")
        for k, lo, hi in (("cap", 1, 10**9), ("heads", 0, 128), ("tails", 0, 128)):
            _integer(getattr(self, k), lo, hi, k)
        try:
            Precision(self.bits, self.log_terms)
        except ValueError as exc:
            raise VerificationError(str(exc)) from exc

    def as_dict(self):
        return dict(operation="envelope", cdf=[str(x) for x in self.cdf], rho=str(self.rho),
                    budget=str(self.budget), cap=self.cap, heads=self.heads, tails=self.tails,
                    bits=self.bits, log_terms=self.log_terms)


@dataclass(frozen=True)
class RoundingRequest:
    atoms: tuple[tuple[F, F], ...]
    subdivisions: int = 16
    rho: F = F(1, 4)
    budget: F = F(256)

    def __post_init__(self):
        validated = fc.Request("prefix", self.atoms, rho=self.rho, budget=self.budget)
        object.__setattr__(self, "atoms", validated.atoms)
        object.__setattr__(self, "rho", validated.rho)
        object.__setattr__(self, "budget", validated.budget)
        _integer(self.subdivisions, 1, 10**6, "subdivisions")

    def as_dict(self):
        return dict(operation="rounding", atoms=[[str(d), str(w)] for d,w in self.atoms],
                    subdivisions=self.subdivisions, rho=str(self.rho), budget=str(self.budget))


@dataclass(frozen=True)
class TransferRequest:
    lower: F
    upper: F
    rounding_factor: F = F(1)
    tv_radius: F = F(0)
    rho: F = F(1, 4)
    budget: F = F(256)

    def __post_init__(self):
        for k in ("lower", "upper", "rounding_factor", "tv_radius", "rho", "budget"):
            object.__setattr__(self, k, dc._exact(getattr(self, k)))
        if (not 0 <= self.lower <= self.upper or self.rounding_factor < 1 or
                not 0 <= self.tv_radius <= 1 or not 0 < self.rho <= F(1, 4) or self.budget <= 0):
            raise VerificationError("Invalid input enclosure, factor, TV radius, rarity or budget.")

    def as_dict(self):
        return dict(operation="transfer", **{k: str(getattr(self,k)) for k in
            ("lower", "upper", "rounding_factor", "tv_radius", "rho", "budget")})


Request = EnvelopeRequest | RoundingRequest | TransferRequest


def produce(r: Request) -> dict:
    if type(r) is EnvelopeRequest:
        env = GapEnvelope(r.cdf)
        split = env.split(r.rho, r.budget, Precision(r.bits,r.log_terms))
        active = env.zero_mass < r.rho
        conditional = (r.rho-env.zero_mass)/(1-env.zero_mass) if active else None
        normalized = env._positive.law if active else None
        core, threshold = quantile_split(normalized,conditional) if active else ((),None)
        out = dict(mode="active" if active else "fallback", zero_mass=str(env.zero_mass),
                   atoms=[[str(d),str(w)] for d,w in env.atoms],
                   normalized=[[str(a.gap),str(a.mass)] for a in normalized.atoms] if active else [],
                   conditional_rho=str(conditional) if active else None,
                   core=[str(s) for s in core], threshold=str(threshold) if active else None,
                   band_costs={str(j):str(a) for j,a in split.band_costs.items()},
                   unresolved_mass=str(split.unresolved_mass), tail_inverse=str(split.tail_inverse),
                   resolved_error=str(split.resolved_error(r.cap)), tail_work=str(split.tail_work(r.cap)),
                   prefix=env.null_prefix(r.heads,r.tails,F(1,2**r.bits)).as_dict())
    elif type(r) is RoundingRequest:
        rounded = round_up_within_bands(FiniteGapLaw(r.atoms), subdivisions=r.subdivisions)
        out = dict(atoms=[[str(a.gap),str(a.mass)] for a in rounded.law.atoms],
                   factor=str(rounded.factor), destinations=[str(x) for x in rounded.destinations])
    elif type(r) is TransferRequest:
        try:
            out = transfer_enclosure(Interval(r.lower,r.upper), rounding_factor=r.rounding_factor,
                                     tv_radius=r.tv_radius,rho=r.rho).as_dict()
        except ValueError as exc:
            raise VerificationError("The legacy transfer returned no ordered interval.") from exc
    else:
        raise VerificationError("Unknown request type.")
    cert = dict(schema=SCHEMA,request=r.as_dict(),output=out)
    _output(r,cert)
    return cert


def _same(a,b):
    if type(a) is not type(b): return False
    if type(b) is dict: return a.keys()==b.keys() and all(_same(a[k],v) for k,v in b.items())
    if type(b) is list: return len(a)==len(b) and all(_same(x,y) for x,y in zip(a,b))
    return a==b


def _number(x):
    if type(x) is not str: raise VerificationError("Output numbers must be exact rational strings.")
    return str(dc._exact(x,dc.MAX_ENDPOINT_BITS))


def _interval_output(x):
    if type(x) is not dict or set(x)!={"lower","upper"}: raise VerificationError("Malformed interval.")
    lo,hi=(_number(x[k]) for k in ("lower","upper"))
    if F(lo)>F(hi): raise VerificationError("Reversed output interval.")
    return dict(lower=lo,upper=hi)


def _atoms_output(xs):
    if type(xs) is not list or len(xs)>16: raise VerificationError("Malformed atom list.")
    if any(type(a) is not list or len(a)!=2 for a in xs): raise VerificationError("Malformed atom pair.")
    result=[[_number(v) for v in a] for a in xs]
    if any(not 0<F(d)<=F(1,2) or F(w)<=0 for d,w in result): raise VerificationError("Invalid positive atom.")
    if len({d for d,_ in result})!=len(result): raise VerificationError("Duplicate output atom.")
    return result


def _output(r: Request, cert: Any) -> dict:
    if type(r) not in (EnvelopeRequest,RoundingRequest,TransferRequest): raise VerificationError("Unknown request type.")
    if type(cert) is not dict or set(cert)!={"schema","request","output"} or type(cert["schema"]) is not str or cert["schema"]!=SCHEMA:
        raise VerificationError("Unknown certificate schema or fields.")
    if not _same(cert["request"],r.as_dict()): raise VerificationError("Certificate does not match the expected request.")
    out=cert["output"]
    if type(r) is TransferRequest: return _interval_output(out)
    fields=({"atoms","factor","destinations"} if type(r) is RoundingRequest else
            {"mode","zero_mass","atoms","normalized","conditional_rho","core","threshold","band_costs",
             "unresolved_mass","tail_inverse","resolved_error","tail_work","prefix"})
    if type(out) is not dict or set(out)!=fields: raise VerificationError("Unexpected output fields.")
    atoms=_atoms_output(out["atoms"])
    if type(r) is RoundingRequest:
        if type(out["destinations"]) is not list or len(out["destinations"])!=len(r.atoms):
            raise VerificationError("One destination is required for every input atom.")
        return dict(atoms=atoms,factor=_number(out["factor"]),destinations=[_number(x) for x in out["destinations"]])
    if type(out["mode"]) is not str or out["mode"] not in ("active","fallback"):
        raise VerificationError("Unknown envelope mode.")
    normalized=_atoms_output(out["normalized"])
    if type(out["core"]) is not list or len(out["core"])!=len(normalized): raise VerificationError("Malformed core.")
    bands=out["band_costs"]
    allowed={str(band_index(F(d))) for d,_ in atoms}
    if type(bands) is not dict or any(type(k) is not str or k not in allowed for k in bands):
        raise VerificationError("Unknown band label.")
    if out["mode"]=="active":
        if not normalized: raise VerificationError("Active mode needs a positive probability law.")
        conditional,threshold=_number(out["conditional_rho"]),_number(out["threshold"])
    else:
        if normalized or out["core"] or out["conditional_rho"] is not None or out["threshold"] is not None:
            raise VerificationError("Fallback must not claim a conditional oracle.")
        conditional=threshold=None
    return dict(mode=out["mode"],atoms=atoms,normalized=normalized,core=[_number(x) for x in out["core"]],
                conditional_rho=conditional,threshold=threshold,band_costs={k:_number(v) for k,v in bands.items()},
                prefix=_interval_output(out["prefix"]),**{k:_number(out[k]) for k in
                    ("zero_mass","unresolved_mass","tail_inverse","resolved_error","tail_work")})


_HEADER="""import ThresholdHC.EnvelopeTransferCertificates.Transfer
open MeasureTheory
open scoped ENNReal BigOperators
open ThresholdHC.Tier6 ThresholdHC.FiniteLawCertificates ThresholdHC.EnvelopeTransferCertificates
open ThresholdHC.DeterministicCertificates ThresholdHC.ArbitraryLawAdaptation
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
"""


def _transfer_proof(r,out):
    i=dc._interval(Interval(r.lower,r.upper));o=dc._interval(Interval(F(out['lower']),F(out['upper'])))
    rr,eta,rho,b=map(dc._q,(r.rounding_factor,r.tv_radius,r.rho,r.budget))
    return f"""theorem certified_value :
    {dc._q(F(out['lower']))} = max 0 ({dc._q(r.lower)}-{eta}) ∧
    {dc._q(F(out['upper']))} = min {rho} ({rr}*{dc._q(r.upper)}+{eta}) ∧
    ∀ (μ μ₀ : Measure Gap) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ₀]
      (T : Gap → Gap), Measurable T → tvDist μ μ₀/2 ≤ ({eta}:ℝ) →
      (∀ d : Gap, (d:ℝ) ≤ (T d:ℝ) ∧ (T d:ℝ) ≤ ({rr}:ℝ)*(d:ℝ)) →
      (∀ j, T ⁻¹' ThresholdHC.EntropyTail.band j = ThresholdHC.EntropyTail.band j) →
      Contains {i} (ThresholdHC.EntropyTail.selection (μ₀.map T) ({rho}:ℝ) ({b}:ℝ)).toReal →
      Contains {o} (ThresholdHC.EntropyTail.selection μ ({rho}:ℝ) ({b}:ℝ)).toReal := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro μ μ₀ _ _ T hm htv hd hb hi
  exact transfer_original μ μ₀ T hm {rr} {eta} {rho} {b}
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) htv hd hb {i} {o} hi
    (by norm_num [transferCheck])
"""


def proof_source(r: Request, certificate: Any) -> str:
    out=_output(r,certificate)
    if type(r) is TransferRequest: body=_transfer_proof(r,out)
    elif type(r) is RoundingRequest: body=_rounding_proof(r,out)
    else: body=_envelope_proof(r,out)
    source=_HEADER+body+"#print axioms certified_value\n"
    if len(source.encode('utf-8'))>dc.MAX_SOURCE_BYTES: raise VerificationError("Proof exceeds the source-size limit.")
    return source


def _rounding_proof(r,out):
    atoms=tuple((F(d),F(w)) for d,w in out['atoms'])
    if not atoms: raise VerificationError("Rounded probability law cannot be empty.")
    destinations=tuple(F(x) for x in out['destinations'])
    indices={d:i for i,(d,_) in enumerate(atoms)}
    if any(d not in indices for d in destinations): raise VerificationError("Destination absent from returned law.")
    route=fc._vec((indices[d] for d in destinations),f"Fin {len(atoms)}")
    g,w=fc._vec(d for d,_ in r.atoms),fc._vec(w for _,w in r.atoms)
    ng,nw=fc._vec(d for d,_ in atoms),fc._vec(w for _,w in atoms)
    dest=fc._vec(destinations);factor=dc._q(F(out['factor']));rho,b=map(dc._q,(r.rho,r.budget))
    pairs='['+', '.join(f'(points gaps hg {i}, points destinations hd {i})' for i in range(len(r.atoms)))+']'
    cases=' | '.join('rfl' for _ in r.atoms)
    bands=[band_index(d) for d,_ in r.atoms]
    band_proofs='\n'.join(f'  · exact ⟨{j}, by norm_num [ThresholdHC.EntropyTail.band, points, gaps, destinations], by norm_num [ThresholdHC.EntropyTail.band, points, gaps, destinations]⟩' for j in bands)
    exact_factor=dc._q(F(1))
    for (d,_),e in zip(r.atoms,destinations): exact_factor=f'max ({exact_factor}) ({dc._q(e/d)})'
    return f"""private def gaps := {g}
private def weights := {w}
private def destinations := {dest}
private def roundedGaps := {ng}
private def roundedWeights := {nw}
private theorem hg : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by norm_num [gaps, Fin.forall_fin_succ]
private theorem hd : ∀ i, 0 < destinations i ∧ destinations i ≤ 1/2 := by norm_num [destinations, Fin.forall_fin_succ]
private theorem hn : ∀ i, 0 < roundedGaps i ∧ roundedGaps i ≤ 1/2 := by norm_num [roundedGaps, Fin.forall_fin_succ]
private theorem hw : ∀ i, 0 ≤ weights i := by norm_num [weights, Fin.forall_fin_succ]
private noncomputable def pairs : List (Gap × Gap) := {pairs}
private noncomputable def transport := pointMap pairs
private noncomputable def law := atomicMeasure (points gaps hg) weights
private noncomputable def rounded := atomicMeasure (points roundedGaps hn) roundedWeights
private theorem bounds : ∀ x : Gap, (x:ℝ) ≤ (transport x:ℝ) ∧ (transport x:ℝ) ≤ ({factor}:ℝ)*(x:ℝ) := by
  apply pointMap_bounds pairs (by norm_num)
  intro p hp
  simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with {cases}
  all_goals norm_num [points, gaps, destinations]
private theorem bands : ∀ j, transport ⁻¹' ThresholdHC.EntropyTail.band j = ThresholdHC.EntropyTail.band j := by
  apply pointMap_bands pairs
  intro p hp
  simp only [pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with {cases}
{band_proofs}
private theorem pushforward : law.map transport = rounded := by
  rw [law, map_atomic_gap _ _ transport (pointMap_measurable pairs)]
  have he : (fun i => transport (points gaps hg i)) = (fun i => points roundedGaps hn ({route} i)) := by
    funext i
    fin_cases i <;> norm_num [transport, pairs, pointMap, points, gaps, destinations, roundedGaps]
  rw [he, atomic_group _ weights hw]
  congr 1
  funext j
  fin_cases j <;> norm_num [weights, roundedWeights, Fin.sum_univ_succ]
theorem certified_value : IsProbabilityMeasure law ∧ IsProbabilityMeasure rounded ∧
    {factor} = {exact_factor} ∧ {factor} ≤ 1+1/({r.subdivisions}:ℚ) ∧
    (∀ i, transport (points gaps hg i) = points destinations hd i) ∧
    law.map transport = rounded ∧
    ThresholdHC.EntropyTail.selection rounded ({rho}:ℝ) ({b}:ℝ) ≤
      ThresholdHC.EntropyTail.selection law ({rho}:ℝ) ({b}:ℝ) ∧
    ThresholdHC.EntropyTail.selection law ({rho}:ℝ) ({b}:ℝ) ≤ ENNReal.ofReal ({factor}:ℝ)*
      ThresholdHC.EntropyTail.selection rounded ({rho}:ℝ) ({b}:ℝ) := by
  have hp : IsProbabilityMeasure law := atomicMeasure_probability _ _ hw (by norm_num [weights, Fin.sum_univ_succ])
  refine ⟨hp, atomicMeasure_probability _ _ (by norm_num [roundedWeights, Fin.forall_fin_succ])
    (by norm_num [roundedWeights, Fin.sum_univ_succ]), by norm_num, by norm_num, ?_, pushforward, ?_⟩
  · intro i
    fin_cases i <;> norm_num [transport, pairs, pointMap, points, gaps, destinations]
  · let : IsProbabilityMeasure law := hp
    rw [← pushforward]
    exact ThresholdHC.SelectionStability.band_preserving_rounding law transport (pointMap_measurable pairs)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) bounds bands
"""


def _envelope_proof(r,out):
    atoms=tuple(sorted((F(d),F(w)) for d,w in out['atoms']))
    g,w=fc._vec(d for d,_ in atoms),fc._vec(w for _,w in atoms)
    z=dc._q(F(out['zero_mass']));rho,b,cap=map(dc._q,(r.rho,r.budget,F(r.cap)))
    cdf=fc._vec(r.cdf);n=len(r.cdf)-1
    prefix=dc._interval(Interval(F(out['prefix']['lower']),F(out['prefix']['upper'])))
    base=f"""private def cdf := {cdf}
private def gaps := {g}
private def weights := {w}
private theorem hg : ∀ i, 0 < gaps i ∧ gaps i ≤ 1/2 := by norm_num [gaps, Fin.forall_fin_succ]
private theorem hw : ∀ i, 0 ≤ weights i := by norm_num [weights, Fin.forall_fin_succ]
private noncomputable def law := envelopeLaw (extendCDF cdf) {n}
private theorem construction : law = extendedAtomic {z} (points gaps hg) weights := by
  simp only [law, envelopeLaw, extendedAtomic, map_atomic _ _ Subtype.val measurable_subtype_coe]
  norm_num [extendCDF, cdf, gridPoint, gaps, weights, points, Fin.sum_univ_succ]
  <;> simp only [add_comm, add_left_comm, add_assoc]
private theorem probability : IsProbabilityMeasure law := by
  rw [construction]
  exact extendedAtomic_probability {z} _ weights (by norm_num) hw
    (by norm_num [weights, Fin.sum_univ_succ])
private theorem prefix_bound : Contains {prefix}
    (∫ x : ℝ, (1/2-x)^{r.heads}*(1/2+x)^{r.tails} ∂law) := by
  rw [construction, extended_integral {z} _ weights (by norm_num) hw]
  norm_num [Contains, points, gaps, weights, Fin.sum_univ_succ]
private theorem cdf_mono : Antitone cdf := by
  norm_num [Antitone, cdf, Fin.forall_fin_succ]
private theorem domination (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hs : μ (Set.Iio 0)=0)
    (hb : ∀ j ≤ {n}, μ.real (Set.Iic (gridPoint j)) ≤ extendCDF cdf j) (x : ℝ) :
    μ (Set.Iic x) ≤ law (Set.Iic x) :=
  envelopeLaw_dominates μ (extendCDF_nonneg cdf (by norm_num [cdf, Fin.forall_fin_succ]))
    (extendCDF_antitone cdf cdf_mono) (by norm_num [extendCDF, cdf]) hs {n} hb x
"""
    common=f"""IsProbabilityMeasure law ∧ law = extendedAtomic {z} (points gaps hg) weights ∧
    law {{0}} = ENNReal.ofReal ({z}:ℝ) ∧
    Contains {prefix} (∫ x : ℝ, (1/2-x)^{r.heads}*(1/2+x)^{r.tails} ∂law) ∧
    ({dc._q(F(out['prefix']['upper']))}:ℝ)-({dc._q(F(out['prefix']['lower']))}:ℝ) ≤ ({dc._q(F(1,2**r.bits))}:ℝ) ∧
    (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], μ (Set.Iio 0)=0 →
      (∀ j ≤ {n}, μ.real (Set.Iic (gridPoint j)) ≤ extendCDF cdf j) →
      ∀ x, μ (Set.Iic x) ≤ law (Set.Iic x)) ∧
"""
    intro=f"""  refine ⟨probability, construction, ?_, prefix_bound, by norm_num, domination, ?_⟩
  · rw [construction, extendedAtomic_zero]
"""
    if out['mode']=='fallback':
        # Callback zeros are placeholders. Only the zero floor/fallback is claimed.
        zeros=' ∧ '.join(f'{dc._q(F(out[k]))} = 0' for k in ('tail_inverse','resolved_error','tail_work'))
        if out['band_costs']: raise VerificationError("Fallback must have no band costs.")
        return base+f"""theorem certified_value : {common}
    ({rho}:ℝ) ≤ ({z}:ℝ) ∧ {dc._q(F(out['unresolved_mass']))} = {z} ∧ {zeros} ∧
    zeroSelection law ({rho}:ℝ) ({b}:ℝ) = ENNReal.ofReal ({rho}:ℝ) := by
{intro}  · refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [construction]
    exact fallback_selection {z} _ weights (by norm_num) (by norm_num) (by norm_num)
"""
    return base+_active_envelope_proof(r,out,atoms,common,intro)


def _active_envelope_proof(r,out,atoms,common,intro):
    normalized=tuple((F(d),F(w)) for d,w in out['normalized'])
    if tuple(d for d,_ in normalized)!=tuple(d for d,_ in atoms):
        raise VerificationError("Normalized law must retain the canonical positive support.")
    core=tuple(F(x) for x in out['core']);t=F(out['threshold']);zv=F(out['zero_mass'])
    nv=tuple(w for _,w in normalized);z=dc._q(zv)
    rho,b,cap,conditional=map(dc._q,(r.rho,r.budget,F(r.cap),F(out['conditional_rho'])))
    boundary=sum((w for d,w in normalized if d==t),F(0))
    if not boundary: raise VerificationError("Quantile threshold is not a positive atom.")
    fraction=(F(out['conditional_rho'])-sum((w for d,w in normalized if d<t),F(0)))/boundary
    labels=tuple(sorted({band_index(d) for d,_ in atoms}))
    costs=fc._vec(F(out['band_costs'].get(str(j),'0')) for j in labels)
    if F(out["tail_work"]) < 0:
        raise VerificationError("Negative tail-work upper bound.")
    claimed=dc._interval(Interval(F(0),F(out['tail_work'])))
    witness=fc._work_evidence(SimpleNamespace(atoms=atoms,budget=r.budget,cap=r.cap,log_terms=r.log_terms),core,F(out['tail_work']))
    reduce='gaps, weights, selected, normalizedWeights, points, Fin.sum_univ_succ, Fin.forall_fin_succ'
    return f"""private def normalizedWeights := {fc._vec(nv)}
private def selected := {fc._vec(core)}
private def labels := {fc._vec(labels,'ℕ')}
private theorem hs : ∀ i, 0 ≤ selected i ∧ selected i ≤ 1 := by norm_num [selected, Fin.forall_fin_succ]
private theorem hws (i) : 0 ≤ weights i*selected i := mul_nonneg (hw i) (hs i).1
private theorem hn : ∀ i, 0 ≤ normalizedWeights i := by norm_num [normalizedWeights, Fin.forall_fin_succ]
private theorem normalization : normalizedWeights = (fun i => weights i/(1-{z})) := by
  funext i
  fin_cases i <;> norm_num [weights, normalizedWeights]
private noncomputable def positivePartLaw := atomicMeasure (points gaps hg) weights
private noncomputable def conditionalLaw := atomicMeasure (points gaps hg) normalizedWeights
private theorem conditional_probability : IsProbabilityMeasure conditionalLaw :=
  atomicMeasure_probability _ _ hn (by norm_num [normalizedWeights, Fin.sum_univ_succ])
private theorem split_rarity : conditionalRarity ({rho}:ℝ) ({z}:ℝ) = ({conditional}:ℝ) := by
  norm_num [conditionalRarity]
private noncomputable def core := ENNReal.ofReal (1-({z}:ℝ)) •
  ThresholdHC.EntropyTailQuantile.quantileCore conditionalLaw (conditionalRarity ({rho}:ℝ) ({z}:ℝ))
private noncomputable def tail := (positivePartLaw-core).restrict {{x : Gap | 1 ≤ ({b}:ℝ)*(x:ℝ)^2}}
private noncomputable def unresolved := (positivePartLaw-core).restrict {{x : Gap | ({b}:ℝ)*(x:ℝ)^2 < 1}}
private theorem core_eq : core = atomicMeasure (points gaps hg) (fun i => weights i*selected i) := by
  rw [core, conditionalLaw, normalization, split_rarity]
  apply scaled_core {z} _ weights selected (by norm_num)
  apply quantileCore_atomic (points gaps hg) (fun i => weights i/(1-{z})) selected
    (by norm_num [{reduce}]) (by norm_num [{reduce}])
    (ρ := ({conditional}:ℝ)) (t := ({dc._q(t)}:ℝ)) (by norm_num) (by norm_num)
    {dc._q(fraction)} (by norm_num)
  all_goals norm_num [{reduce}]
private theorem tail_eq : tail = atomicMeasure (points gaps hg) (tailWeights gaps weights selected {b}) := by
  rw [tail, core_eq]
  exact tailMeasure_eq gaps weights selected {b} hg hw hs
private theorem unresolved_eq : unresolved = atomicMeasure (points gaps hg) (unresolvedWeights gaps weights selected {b}) := by
  rw [unresolved, core_eq]
  exact unresolvedMeasure_eq gaps weights selected {b} hg hw hs
private theorem resolved_eq : core+tail = atomicMeasure (points gaps hg) (resolvedWeights gaps weights selected {b}) := by
  rw [tail, core_eq]
  exact resolvedMeasure_eq gaps weights selected {b} hg hw hs
theorem certified_value : {common}
    ({z}:ℝ) < ({rho}:ℝ) ∧ IsProbabilityMeasure conditionalLaw ∧
    law = zeroAtomLaw ({z}:ℝ) conditionalLaw ∧
    conditionalRarity ({rho}:ℝ) ({z}:ℝ) = ({conditional}:ℝ) ∧
    ThresholdHC.EntropyTailQuantile.quantileThreshold conditionalLaw ({conditional}:ℝ) = ({dc._q(t)}:ℝ) ∧
    core = atomicMeasure (points gaps hg) (fun i => weights i*selected i) ∧
    (∀ j, ThresholdHC.EntropyTail.bandCost core (labels j) = ENNReal.ofReal ({costs} j:ℝ)) ∧
    ({z}:ℝ)+unresolved.real Set.univ = ({dc._q(F(out['unresolved_mass']))}:ℝ) ∧
    (∫ x : Gap, (x:ℝ)⁻¹ ∂tail) = ({dc._q(F(out['tail_inverse']))}:ℝ) ∧
    (∫ x : Gap, min 1 (1/(({cap}:ℝ)*(x:ℝ)^2)^2) ∂(core+tail)) = ({dc._q(F(out['resolved_error']))}:ℝ) ∧
    Contains {claimed} (tailWorkIntegral tail ({cap}:ℝ)) := by
{intro}  · refine ⟨by norm_num, conditional_probability, ?_, split_rarity, ?_, core_eq, ?_, ?_, ?_, ?_, ?_⟩
    · rw [construction, normalized_identity {z} _ weights (by norm_num), conditionalLaw, normalization]
    · let : IsProbabilityMeasure conditionalLaw := conditional_probability
      apply quantileThreshold_eq_of_mass conditionalLaw (ρ := ({conditional}:ℝ)) (by norm_num) (by norm_num)
      all_goals rw [conditionalLaw, atomicMeasure_real _ _ hn]
      all_goals norm_num [{reduce}]
    · intro j
      rw [core_eq, bandCost_atomic _ _ hws]
      fin_cases j <;> norm_num [labels, ThresholdHC.EntropyTail.band, {reduce}]
    · rw [unresolved_eq, atomicMeasure_real _ _ (by norm_num [unresolvedWeights, {reduce}])]
      norm_num [unresolvedWeights, {reduce}]
    · rw [tail_eq, inverseIntegral_eq gaps _ hg (tailWeights_nonneg gaps weights selected {b} hw hs)]
      norm_num [inverseValue, tailWeights, {reduce}]
    · rw [resolved_eq, errorIntegral_eq gaps _ {cap} hg (by intro i; exact add_nonneg (hws i) (tailWeights_nonneg gaps weights selected {b} hw hs i))]
      norm_num [errorValue, resolvedWeights, tailWeights, {reduce}]
    · rw [tail_eq]
      apply tailWork_accepted_sound gaps _ {cap} hg (tailWeights_nonneg gaps weights selected {b} hw hs) (c := {witness})
      norm_num [{reduce}, {fc._REDUCE}]
"""


def verify(r: Request, certificate: Any, *, lean_dir: Path, timeout: float=240) -> dict:
    output=_output(r,certificate)
    source=proof_source(r,dict(schema=SCHEMA,request=r.as_dict(),output=output))
    if type(timeout) not in (int,float) or not 0<timeout<=600: raise VerificationError("Timeout must lie in (0,600].")
    try:
        run=subprocess.run(['lake','env','lean','--stdin'],cwd=lean_dir,input=source,text=True,encoding='utf-8',
                           capture_output=True,timeout=timeout,check=False)
    except (OSError,subprocess.TimeoutExpired) as exc:
        raise VerificationError("Kernel execution unavailable or verification resource limit reached.") from exc
    report=run.stdout+run.stderr
    try: dc.validate_kernel_report(report,run.returncode,sqrt=False)
    except VerificationError as exc:
        exc.kernel_report=report
        raise
    return dict(verified=True,request=r.as_dict(),output=output,proof_source=source,kernel_report=report,
                proof_sha256=hashlib.sha256(source.encode('utf-8')).hexdigest(),
                scope='envelope_rounding_or_conditional_transfer_not_statistical_execution',
                transfer_premises_verified=False,python_execution_verified=False,external_compiled_cache_trusted=True)
