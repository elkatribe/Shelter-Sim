import React, { useState, useMemo, useCallback } from "react";
import {
  LineChart, Line, XAxis, YAxis, CartesianGrid, Tooltip, ResponsiveContainer,
  ReferenceLine, ReferenceArea, Area, ComposedChart,
} from "recharts";

/* ============================================================================
   DETERMINISTIC SHELTER POPULATION MANAGEMENT SIMULATION
   Agent-based, daily time-stepping. Seeded baseline; Run projects 12 months
   forward; Reset returns to baseline; consecutive Runs chain from end state.
   LOS = outcome day - intake day + 1. In-care censored at report day.
   All parameter mappings are ILLUSTRATIVE general-principle multipliers.
   ============================================================================ */

const BASE = {
  dog: {
    label: "Dogs", dailyIntake: 7, strayFraction: 0.65, cfc: 183, physicalMax: 366,
    census: 155, alos: 22.17,
    mix: { adoption: 0.625, rto: 0.065, transfer: 0.16, euthanasia: 0.10, died: 0.05, rtf: 0.0 },
    los: { adoption: 31, rto: 3, transfer: 10, euthanasia: 7, died: 6, rtf: 3 },
    settleDays: 45,
    diseaseBaseline: 0.04, diseaseName: "CIRD",
  },
  cat: {
    label: "Cats", dailyIntake: 7, strayFraction: 0.70, cfc: 113, physicalMax: 226,
    census: 96, alos: 13.75,
    mix: { adoption: 0.52, rto: 0.02, transfer: 0.26, euthanasia: 0.13, died: 0.07, rtf: 0.0 },
    los: { adoption: 17, rto: 3, transfer: 12, euthanasia: 9, died: 8, rtf: 3 },
    settleDays: 45,
    diseaseBaseline: 0.08, diseaseName: "Feline URI",
  },
};

const KEYS = ["adoption", "rto", "transfer", "euthanasia", "died", "rtf"];
const LIVE = ["adoption", "rto", "transfer", "rtf"];

const COUPLING = { threshold: 1.0, fullStressRatio: 1.6, maxLosStretch: 0.60, maxAdoptDrop: 0.40 };
const BARRIER_LOS_MULT = { low: 0.75, medium: 1.0, high: 1.30 };
const BARRIER_RATE_MULT = { low: 1.12, medium: 1.0, high: 0.85 };
const PROJECTION_DAYS = 365;

const clamp = (x, lo, hi) => Math.max(lo, Math.min(hi, x));

// Respiratory-disease prevalence model (illustrative). Prevalence = baseline
// + convex doubling term + density term, capped. Convex exponent makes low
// doubling nearly harmless and high doubling steeply harmful.
const DISEASE = { ceiling: 0.38, exponent: 2.5, kDouble: 0.34, kDensity: 0.30 };
// Disease -> outcome coupling: affected animals leave the adoptable pool and
// carry a medical hold. These scale with prevalence above baseline.
const DISEASE_ADOPT_DROP = 0.9;   // at full ceiling prevalence, adoption rate * (1 - 0.9*excess)
const DISEASE_LOS_ADD = 22;       // extra adoption-LOS days at full excess prevalence

// Outcome-rate couplings (ALWAYS ON, so LRR/save rate always reflect crowding).
// Euthanasia-for-space: zero at/below C4C, rising to SPACE_EUTH_MAX as occupancy
// approaches physical capacity (all units doubled).
const SPACE_EUTH_MAX = 0.35;      // max added euthanasia fraction at full physical crowding
// Disease-driven medical mortality: excess respiratory prevalence adds to died/euth.
const DISEASE_DIED_K = 0.20;      // died-in-care add per unit excess prevalence
const DISEASE_EUTH_K = 0.33;      // medical euthanasia add per unit excess prevalence

function diseasePrevalence(base, doublePct, occ) {
  const dTerm = DISEASE.kDouble * Math.pow(clamp(doublePct, 0, 1), DISEASE.exponent);
  const densTerm = DISEASE.kDensity * Math.max(0, occ - 1);
  return Math.min(DISEASE.ceiling, base + dTerm + densTerm);
}

const C = {
  ink: "#1f1d1a", paper: "#f6f2ea", panel: "#ffffff", line: "#e3ddd0",
  sub: "#726c61", dog: "#a8452c", cat: "#2e6f92", accent: "#2f7d5b",
  warn: "#bb3a24", cfc: "#c2952f", settle: "#efe8d8",
};

/* ---------------------------------------------------------------------------
   SEED starting in-care population as remaining-life cohorts.
--------------------------------------------------------------------------- */
function seedState(speciesBase) {
  const schedule = {};
  let census = 0;
  const inCareCohorts = [];
  KEYS.forEach((k) => {
    const perDay = speciesBase.dailyIntake * speciesBase.mix[k];
    if (perDay <= 0) return;
    const L = Math.max(1, Math.round(speciesBase.los[k]));
    for (let r = 0; r < L; r++) {
      schedule[r] = schedule[r] || {};
      schedule[r][k] = (schedule[r][k] || 0) + perDay;
      census += perDay;
      // tag cohort with pathway + true LOS so realized LOS logs correctly; it is
      // scheduled to exit r days into the projection.
      inCareCohorts.push({ intakeDay: -(L - r), count: perDay, los: L, path: k, scheduledOut: r });
    }
  });
  return { schedule, census, inCareCohorts };
}

/* ---------------------------------------------------------------------------
   PROJECT `days` forward from a start state (seed or chained).
--------------------------------------------------------------------------- */
function project(speciesBase, levers, startState, days) {
  const {
    barrier, holdExtraDays, doublingPct, rtoStrayPct,
    rtfStrayPct, fosterCapacity, couplingOn, cfcOverride, physicalOverride,
  } = levers;

  const rfEligible = speciesBase === BASE.cat; // RTF hard-gated to cats
  const humaneCfc = cfcOverride ?? speciesBase.cfc;      // humane double-compartment capacity
  const physicalMax = physicalOverride ?? speciesBase.physicalMax; // all units doubled
  const dbl = clamp(doublingPct || 0, 0, 1);
  // Effective housing ceiling rises as units are doubled up (portals/guillotines closed).
  const effCapacity = humaneCfc + dbl * (physicalMax - humaneCfc);
  // Absolute daily intake per species (animals/day).
  const dailyIntake = speciesBase === BASE.dog ? levers.intakeDog : levers.intakeCat;
  const strayFrac = speciesBase.strayFraction;

  function baseShares() {
    let m = { ...speciesBase.mix };
    // RTO stray-% lever applies to DOGS only; cats keep their static baseline RTO.
    if (speciesBase === BASE.dog) m.rto = clamp(rtoStrayPct, 0, 1) * strayFrac;
    // RTF is expressed as % of stray intake, cats only.
    if (rfEligible) m.rtf = clamp(rtfStrayPct, 0, 1) * strayFrac;
    // Adoption is the residual after all other pathways, then barrier-adjusted.
    const others = m.rto + m.transfer + m.euthanasia + m.died + (m.rtf || 0);
    m.adoption = Math.max(0, 1 - others);
    m.adoption *= BARRIER_RATE_MULT[barrier];
    const tot = KEYS.reduce((s, k) => s + m[k], 0);
    KEYS.forEach((k) => (m[k] /= tot));
    return m;
  }

  const leaving = Array.from({ length: days + 400 }, () => ({}));
  Object.entries(startState.schedule).forEach(([off, paths]) => {
    const d = +off;
    if (d >= 0 && d < leaving.length) {
      Object.entries(paths).forEach(([k, n]) => { leaving[d][k] = (leaving[d][k] || 0) + n; });
    }
  });

  let census = startState.census;
  let inCare = startState.inCareCohorts.map((c) => ({ ...c }));

  const series = [];
  const monthly = [];
  let monthStartCensus = census, monthIntake = 0, monthLive = 0, monthNonlive = 0, monthOutcomes = 0;
  const recentOutcomes = [];

  for (let d = 0; d < days; d++) {
    // Occupancy is measured against HUMANE capacity: doubling up raises the
    // ceiling but crowding stress is still relative to humane housing.
    const occ = census / humaneCfc;

    // Respiratory disease prevalence: driven by doubling-up (single-compartment
    // housing) plus density. This is the visible hinge of the vicious cycle.
    const prevalence = diseasePrevalence(speciesBase.diseaseBaseline, dbl, occ);
    const excess = Math.max(0, prevalence - speciesBase.diseaseBaseline); // 0..~0.34

    // Disease -> LOS/adoptability spiral. Gated behind the crowding-cycle toggle
    // so students can isolate the length-of-stay feedback dynamic.
    let adoptDrop = 0, losAdd = 0;
    if (couplingOn) {
      adoptDrop = clamp(excess * DISEASE_ADOPT_DROP, 0, 0.9);
      losAdd = excess * DISEASE_LOS_ADD;
    }

    let shares = baseShares();
    if (adoptDrop > 0) {
      const lost = shares.adoption * adoptDrop;
      shares.adoption -= lost;
      shares.euthanasia += lost * 0.6;
      shares.died += lost * 0.4;
    }

    // ALWAYS-ON outcome-rate couplings, so LRR and save rate always reflect crowding:
    //  (a) euthanasia-for-space rises once occupancy exceeds C4C, steepening toward
    //      physical capacity; (b) respiratory disease raises medical died/euthanasia.
    const physRatio = physicalMax / humaneCfc;
    let spaceEuth = 0;
    if (occ > 1 && physRatio > 1) {
      spaceEuth = clamp((occ - 1) / (physRatio - 1), 0, 1) * SPACE_EUTH_MAX;
    }
    const diseaseDied = excess * DISEASE_DIED_K;
    const diseaseEuth = excess * DISEASE_EUTH_K;
    const addEuth = spaceEuth + diseaseEuth;
    const addDied = diseaseDied;
    if (addEuth > 0 || addDied > 0) {
      // Added non-live outcomes come out of the live pool (adoption first, then
      // the other live pathways proportionally), never exceeding what's available.
      const totalAdd = addEuth + addDied;
      const livePool = shares.adoption + shares.rto + shares.transfer + shares.rtf;
      const draw = Math.min(totalAdd, livePool * 0.98);
      // proportional reduction across live pathways
      const scale = livePool > 0 ? (livePool - draw) / livePool : 0;
      shares.adoption *= scale; shares.rto *= scale; shares.transfer *= scale; shares.rtf *= scale;
      // distribute the drawn amount into euth/died in their requested ratio
      const euthShare = totalAdd > 0 ? addEuth / totalAdd : 0;
      shares.euthanasia += draw * euthShare;
      shares.died += draw * (1 - euthShare);
    }

    const eLos = { ...speciesBase.los };
    eLos.adoption = eLos.adoption * BARRIER_LOS_MULT[barrier] + holdExtraDays + losAdd;
    eLos.transfer = eLos.transfer + holdExtraDays * 0.5;

    KEYS.forEach((k) => {
      const n = dailyIntake * shares[k];
      if (n <= 0) return;
      const stay = Math.max(1, Math.round(eLos[k]));
      leaving[d + stay][k] = (leaving[d + stay][k] || 0) + n;
      inCare.push({ intakeDay: d, count: n, los: stay, path: k, scheduledOut: d + stay });
    });
    census += dailyIntake;
    monthIntake += dailyIntake;

    const leftToday = leaving[d];
    let leftTotal = 0, liveToday = 0, nonliveToday = 0;
    KEYS.forEach((k) => {
      const n = leftToday[k] || 0;
      if (n <= 0) return;
      leftTotal += n;
      if (LIVE.includes(k)) liveToday += n; else nonliveToday += n;
      // remove n animals of pathway k scheduled out today; log their true LOS
      let rem = n;
      for (let i = 0; i < inCare.length && rem > 1e-9; i++) {
        const ic = inCare[i];
        if (ic.path === k && Math.abs(ic.scheduledOut - d) < 0.5) {
          const take = Math.min(ic.count, rem);
          recentOutcomes.push({ day: d, los: ic.los, count: take });
          ic.count -= take; rem -= take;
        }
      }
    });
    census -= leftTotal;
    monthLive += liveToday;
    monthNonlive += nonliveToday;
    monthOutcomes += leftTotal;
    inCare = inCare.filter((c) => c.count > 1e-9);

    while (recentOutcomes.length && recentOutcomes[0].day < d - 30) recentOutcomes.shift();
    let rSum = 0, rCnt = 0;
    recentOutcomes.forEach((o) => { rSum += o.los * o.count; rCnt += o.count; });
    const rollingAlos = rCnt > 0 ? rSum / rCnt : speciesBase.alos;

    const fosterCount = Math.min(fosterCapacity, Math.max(0, census - humaneCfc));
    const housed = census - fosterCount;

    let cSum = 0, cCnt = 0;
    inCare.forEach((c) => { cSum += c.count * (d - c.intakeDay + 1); cCnt += c.count; });
    const censoredAlos = cCnt > 0 ? cSum / cCnt : 0;

    series.push({
      day: d + 1,
      census: +census.toFixed(1),
      housed: +housed.toFixed(1),
      foster: +fosterCount.toFixed(1),
      rollingAlos: +rollingAlos.toFixed(2),
      censoredAlos: +censoredAlos.toFixed(2),
      occ: +(census / humaneCfc).toFixed(3),
      disease: +(prevalence * 100).toFixed(1),
    });

    if ((d + 1) % 30 === 0) {
      // LRR (SAC) = live outcomes / total outcomes
      const lrr = monthOutcomes > 0 ? (monthLive / monthOutcomes) * 100 : 0;
      // Save rate = (intakes - non-live outcomes) / intakes
      const save = monthIntake > 0 ? ((monthIntake - monthNonlive) / monthIntake) * 100 : 0;
      monthly.push({
        month: Math.round((d + 1) / 30),
        lrr: +lrr.toFixed(1),
        save: +clamp(save, 0, 100).toFixed(1),
      });
      monthStartCensus = census; monthIntake = 0; monthLive = 0; monthNonlive = 0; monthOutcomes = 0;
    }
  }

  const endSchedule = {};
  for (let d = days; d < leaving.length; d++) {
    const off = d - days;
    Object.entries(leaving[d]).forEach(([k, n]) => {
      if (n > 1e-9) { endSchedule[off] = endSchedule[off] || {}; endSchedule[off][k] = (endSchedule[off][k] || 0) + n; }
    });
  }
  const endInCare = inCare.map((c) => ({
    intakeDay: c.intakeDay - days, count: c.count,
    los: c.los, path: c.path, scheduledOut: c.scheduledOut - days,
  }));
  const endState = { schedule: endSchedule, census, inCareCohorts: endInCare };

  const avgCensus = series.reduce((s, r) => s + r.census, 0) / series.length;
  const last = series[series.length - 1];

  // Settled steady-state = mean over the last 30 days (the value the lever drives
  // the system TO, not day 365 of a possibly still-moving run).
  const tail = series.slice(-30);
  const settledCensus = tail.reduce((s, r) => s + r.census, 0) / tail.length;
  const settledHoused = tail.reduce((s, r) => s + r.housed, 0) / tail.length;
  const settledAlos = tail.reduce((s, r) => s + r.rollingAlos, 0) / tail.length;
  const settledOcc = settledCensus / humaneCfc;
  // has it actually settled? compare two late windows
  const w1 = series.slice(300, 330), w2 = series.slice(335, 365);
  const m1 = w1.reduce((s, r) => s + r.census, 0) / Math.max(1, w1.length);
  const m2 = w2.reduce((s, r) => s + r.census, 0) / Math.max(1, w2.length);
  const settled = Math.abs(m2 - m1) / Math.max(1, m1) < 0.02;
  const peakOcc = series.reduce((m, r) => Math.max(m, r.occ), 0);
  const settledDisease = tail.reduce((s, r) => s + r.disease, 0) / tail.length;

  return {
    series, monthly, endState,
    summary: {
      cfc: humaneCfc, physicalMax, effCapacity: +effCapacity.toFixed(0),
      dailyIntake: +dailyIntake.toFixed(2),
      avgCensus: +avgCensus.toFixed(1),
      finalCensus: last.census,
      finalOcc: last.occ,
      daysOverCFC: series.filter((r) => r.census > humaneCfc).length,
      finalRollingAlos: last.rollingAlos,
      settleDays: speciesBase.settleDays,
      settledCensus: +settledCensus.toFixed(1),
      settledHoused: +settledHoused.toFixed(1),
      staffHours: +(settledHoused * 15 / 60).toFixed(1),
      settledAlos: +settledAlos.toFixed(2),
      settledOcc: +settledOcc.toFixed(3),
      settledLrr: monthly[monthly.length - 1].lrr,
      settledSave: monthly[monthly.length - 1].save,
      settledDisease: +settledDisease.toFixed(1),
      diseaseBaseline: +(speciesBase.diseaseBaseline * 100).toFixed(1),
      diseaseName: speciesBase.diseaseName,
      settled,
      peakOcc: +peakOcc.toFixed(3),
    },
  };
}

/* --------------------------------------------------------------------------- */
const DEFAULT_LEVERS = {
  intakeDog: 7, intakeCat: 7, barrier: "medium", holdExtraDays: 0, doublingPct: 0,
  rtoStrayPct: 0.10, rtfStrayPct: 0, fosterCapacity: 0, couplingOn: false,
  cfcOverride: null, physicalOverride: null,
};

// Fixed baseline reference, computed once, for before/after comparison.
const BASELINE_REF = {
  dog: project(BASE.dog, DEFAULT_LEVERS, seedState(BASE.dog), PROJECTION_DAYS).summary,
  cat: project(BASE.cat, DEFAULT_LEVERS, seedState(BASE.cat), PROJECTION_DAYS).summary,
};

/* --------------------------------------------------------------------------- */
const SCENARIOS = [
  { key: "baseline", name: "1. Baseline", title: "Baseline calibration",
    body: "Leave every lever at its default and run. Dog and cat intake at 7/day, adoption barrier Medium, dog RTO 10% of stray intake, cat RTO fixed at 2%, no RTF, no extra hold days, no doubling up, foster capacity 0, crowding cycle off. Confirm that census holds near 155 dogs and 96 cats across the year, and that intake x ALOS reproduces the census. This is your reference point for every other scenario.",
    values: true },
  { key: "transfer", name: "2. Doubling up", title: "Closing the transfer doors (doubling up)",
    body: "Census is running high and you don't want to turn animals away, so you start closing the guillotine doors between double-compartment kennels (and the portals between cat cages), housing two animals where one belonged. This buys you space: effective capacity climbs toward the physical maximum. Raise the doubling-up slider and turn the crowding cycle on. Watch respiratory disease (CIRD in dogs, feline URI in cats) climb as single-compartment housing spreads, which drags down adoptions and lengthens stays, feeding the very crowding you were trying to relieve. Try a low level first (relatively safe) and then push it high.",
    values: true },
  { key: "barrier", name: "3. Adoption barrier", title: "Adoption barrier reduction",
    body: "You have dropped adoption fees, opened evening hours, and simplified the application. Set the adoption barrier to Low and leave everything else at default. Watch ALOS and census fall. Note that reducing barriers here does not change intake or return rates, only how quickly adoptable animals move out.",
    values: true },
  { key: "diversion", name: "4. Intake diversion", title: "Intake diversion / safety net",
    body: "New owner-support, pet-retention, and managed-intake programs are keeping animals out of the shelter altogether. Lower the dog and cat intake sliders (animals per day) and run. Compare this front-door approach with the throughput approach from the adoption-barrier scenario: both relieve census, but they act on different points in the flow.",
    values: false },
  { key: "bottleneck", name: "5. LOS bottleneck", title: "Length-of-stay bottleneck",
    body: "A medical or behavior backlog is holding animals longer before they can be made available for adoption. Add extra hold days at unchanged intake and run. Then try turning the crowding cycle on to see how a processing bottleneck and overcrowding reinforce one another.",
    values: false },
  { key: "foster", name: "6. Foster expansion", title: "Foster expansion",
    body: "A foster recruitment push has given you off-site capacity. Raise foster capacity and run. Watch housed occupancy fall against Capacity for Care even though the outcome mix is unchanged. Foster moves animals out of the building without changing how their stays end.",
    values: false },
  { key: "cfcphys", name: "7. C4C vs. physical", title: "Capacity for Care (C4C) vs. physical capacity",
    body: "Humane capacity (C4C) and physical cage count are not the same number. Use the doubling-up slider to raise effective capacity above C4C while staying below the physical maximum, and turn the crowding cycle on. Notice that welfare breaks down at C4C (disease climbs, adoptions fall) long before you literally run out of cages. Humane capacity is the binding constraint, not the wall.",
    values: false },
  { key: "rtf", name: "8. RTF (cats)", title: "Return-to-field for cats",
    body: "Stand up a return-to-field program for healthy free-roaming community cats: sterilize, vaccinate, ear-tip, and return. Route a share of cat intake to RTF (a short three-day pathway) and run. Watch cat ALOS and census drop. As a follow-on, chain a run where census is high enough to tempt doubling up, and see whether RTF's shorter stays keep you off the doubling-up slider altogether.",
    values: false },
  { key: "sandbox", name: "9. Sandbox", title: "Open sandbox",
    body: "No prescribed condition. Combine any levers you like and chain runs together to design and test your own sequence of interventions. Use Reset to baseline whenever you want to start the shelter over.",
    values: false },
];

/* --------------------------------------------------------------------------- */
function Stat({ label, value, sub, tone }) {
  return (
    <div style={{ background: C.panel, border: "1px solid " + C.line, borderRadius: 8, padding: "10px 12px" }}>
      <div style={{ fontSize: 10.5, letterSpacing: ".06em", textTransform: "uppercase", color: C.sub }}>{label}</div>
      <div style={{ fontSize: 22, fontWeight: 700, color: tone || C.ink, lineHeight: 1.1, marginTop: 3 }}>{value}</div>
      {sub && <div style={{ fontSize: 11.5, color: C.sub, marginTop: 2 }}>{sub}</div>}
    </div>
  );
}

// ---- Comparison-first components -----------------------------------------

// Bar showing baseline vs result, with the delta called out.
function CompareBar({ label, baseline, result, unit, color, higherIsBetter, max }) {
  const delta = result - baseline;
  const scaleMax = max || Math.max(baseline, result) * 1.15 || 1;
  const bw = (v) => Math.max(2, (v / scaleMax) * 100);
  // color the delta by direction + whether that direction is good
  const good = higherIsBetter ? delta >= 0 : delta <= 0;
  const deltaColor = Math.abs(delta) < 0.05 ? C.sub : good ? C.accent : C.warn;
  const fmt = (v) => unit === "%" ? Math.round(v) + "%" : (Math.round(v * 100) / 100);
  const sign = delta > 0 ? "+" : "";
  return (
    <div style={{ marginBottom: 12 }}>
      <div style={{ display: "flex", justifyContent: "space-between", alignItems: "baseline", marginBottom: 4 }}>
        <span style={{ fontSize: 12.5, fontWeight: 600, color: C.ink }}>{label}</span>
        <span style={{ fontSize: 12.5, color: deltaColor, fontWeight: 700 }}>
          {Math.abs(delta) < 0.05 ? "no change" : sign + fmt(delta) + (unit === "%" ? " pts" : "")}
        </span>
      </div>
      <div style={{ display: "grid", gridTemplateColumns: "82px 1fr", gap: 8, alignItems: "center", marginBottom: 3 }}>
        <span style={{ fontSize: 10, color: C.sub, lineHeight: 1.1 }}>baseline</span>
        <div style={{ background: C.line, borderRadius: 4, height: 16, position: "relative" }}>
          <div style={{ width: bw(baseline) + "%", height: "100%", background: C.sub, opacity: .5, borderRadius: 4 }} />
          <span style={{ position: "absolute", right: 6, top: 0, fontSize: 10.5, lineHeight: "16px", color: C.ink }}>{fmt(baseline)}</span>
        </div>
      </div>
      <div style={{ display: "grid", gridTemplateColumns: "82px 1fr", gap: 8, alignItems: "center" }}>
        <span style={{ fontSize: 10, color: C.sub, lineHeight: 1.1 }}>after intervention</span>
        <div style={{ background: C.line, borderRadius: 4, height: 16, position: "relative" }}>
          <div style={{ width: bw(result) + "%", height: "100%", background: color, borderRadius: 4 }} />
          <span style={{ position: "absolute", right: 6, top: 0, fontSize: 10.5, lineHeight: "16px", color: C.ink, fontWeight: 600 }}>{fmt(result)}</span>
        </div>
      </div>
    </div>
  );
}

// Occupancy gauge: dot on a safe -> over-C4C -> physical scale.
function OccupancyGauge({ occ, peakOcc, color }) {
  const pct = clamp(occ, 0, 2);
  const pos = (pct / 2) * 100;
  const peakPos = (clamp(peakOcc, 0, 2) / 2) * 100;
  const zone = occ >= 1 ? C.warn : occ >= 0.9 ? C.cfc : C.accent;
  const zoneLabel = occ >= 1 ? "over C4C" : occ >= 0.9 ? "near C4C" : "within C4C";
  return (
    <div style={{ marginBottom: 6 }}>
      <div style={{ display: "flex", justifyContent: "space-between", marginBottom: 6 }}>
        <span style={{ fontSize: 12.5, fontWeight: 600 }}>Occupancy</span>
        <span style={{ fontSize: 13, fontWeight: 700, color: zone }}>{Math.round(occ * 100)}% &middot; {zoneLabel}</span>
      </div>
      <div style={{ position: "relative", height: 14, borderRadius: 7, overflow: "hidden",
        background: "linear-gradient(90deg," + C.accent + " 0%," + C.accent + " 40%," + C.cfc + " 45%," + C.warn + " 50%," + C.warn + " 100%)" }}>
        {/* C4C marker at 100% => 50% of a 0..2 scale */}
        <div style={{ position: "absolute", left: "50%", top: 0, bottom: 0, width: 2, background: C.ink }} />
        {peakOcc > occ + 0.02 && (
          <div style={{ position: "absolute", left: peakPos + "%", top: -2, bottom: -2, width: 2, background: C.ink, opacity: .4 }} />
        )}
        <div style={{ position: "absolute", left: "calc(" + pos + "% - 6px)", top: 1, width: 12, height: 12,
          borderRadius: "50%", background: "#fff", border: "2px solid " + C.ink }} />
      </div>
      <div style={{ display: "flex", justifyContent: "space-between", fontSize: 9.5, color: C.sub, marginTop: 3 }}>
        <span>0%</span><span>C4C (100%)</span><span>200%</span>
      </div>
      {peakOcc > occ + 0.02 && (
        <div style={{ fontSize: 10.5, color: C.sub, marginTop: 4 }}>Peak during year: {Math.round(peakOcc * 100)}% (faint marker)</div>
      )}
    </div>
  );
}

function SpeciesComparison({ label, color, res, ref }) {
  const s = res.summary;
  return (
    <div style={{ background: C.paper, border: "1px solid " + C.line, borderRadius: 12, padding: 16 }}>
      <div style={{ display: "flex", alignItems: "center", gap: 9, marginBottom: 14 }}>
        <span style={{ width: 11, height: 11, borderRadius: 3, background: color }} />
        <h3 style={{ margin: 0, fontSize: 17 }}>{label}</h3>
        {!s.settled && (
          <span style={{ fontSize: 10.5, color: C.warn, border: "1px solid " + C.warn, borderRadius: 10, padding: "1px 8px", fontFamily: "system-ui,sans-serif" }}>
            still moving at 12 mo
          </span>
        )}
      </div>
      <OccupancyGauge occ={s.settledOcc} peakOcc={s.peakOcc} color={color} />
      <div style={{ display: "flex", justifyContent: "space-between", alignItems: "baseline", margin: "10px 0 2px" }}>
        <span style={{ fontSize: 12.5, fontWeight: 600 }}>{s.diseaseName} prevalence</span>
        <span style={{ fontSize: 15, fontWeight: 700, color: s.settledDisease > s.diseaseBaseline + 2 ? C.warn : C.sub }}>
          {s.settledDisease}%
        </span>
      </div>
      <div style={{ fontSize: 10.5, color: C.sub, marginBottom: 4 }}>
        baseline {s.diseaseBaseline}% &middot; {s.effCapacity > s.cfc ? "effective capacity " + s.effCapacity + " (doubled up)" : "humane housing"}
      </div>
      <div style={{ height: 1, background: C.line, margin: "12px 0" }} />
      <CompareBar label="Census (animals)" baseline={ref.settledCensus} result={s.settledCensus}
        color={color} higherIsBetter={false} max={Math.max(s.physicalMax, ref.settledCensus) * 1.05} />
      <CompareBar label="ALOS (days)" baseline={ref.settledAlos} result={s.settledAlos}
        color={color} higherIsBetter={false} />
      <CompareBar label="Live release rate (SAC)" baseline={ref.settledLrr} result={s.settledLrr}
        unit="%" color={color} higherIsBetter={true} max={100} />
      <CompareBar label="Save rate" baseline={ref.settledSave} result={s.settledSave}
        unit="%" color={color} higherIsBetter={true} max={100} />
    </div>
  );
}

// Plain-language LRR + save-rate delta summary per species.
function LrrDeltaNote({ dog, cat, refs }) {
  const cell = (val, ref) => {
    const d = +(val - ref).toFixed(1);
    const col = Math.abs(d) < 0.1 ? C.sub : d > 0 ? C.accent : C.warn;
    const dir = Math.abs(d) < 0.1 ? "unchanged" : (d > 0 ? "+" : "") + d + " pts";
    return <span><strong style={{ color: col }}>{val}%</strong> <span style={{ color: col }}>({dir})</span></span>;
  };
  const row = (label, s, ref) => (
    <div style={{ marginTop: 4 }}>
      <strong style={{ display: "inline-block", width: 42 }}>{label}:</strong>{" "}
      Live Release Rate {ref.settledLrr}% &rarr; {cell(s.settledLrr, ref.settledLrr)}
      <span style={{ margin: "0 8px", color: C.line }}>|</span>
      Save Rate {ref.settledSave}% &rarr; {cell(s.settledSave, ref.settledSave)}
    </div>
  );
  return (
    <div style={{ background: C.panel, border: "1px solid " + C.line, borderLeft: "3px solid " + C.cat, borderRadius: 6, padding: "10px 14px", fontSize: 13, fontFamily: "system-ui,sans-serif" }}>
      <span style={{ fontSize: 11, letterSpacing: ".06em", textTransform: "uppercase", color: C.sub }}>Outcome rates</span>
      {row("Cats", cat, refs.cat)}
      {row("Dogs", dog, refs.dog)}
    </div>
  );
}

// Staff time for basic care: 15 min per in-shelter animal per day.
function StaffTimePanel({ dog, cat, refs }) {
  const total = dog.staffHours + cat.staffHours;
  const baseTotal = refs.dog.staffHours + refs.cat.staffHours;
  const delta = +(total - baseTotal).toFixed(1);
  const col = Math.abs(delta) < 0.1 ? C.sub : delta > 0 ? C.warn : C.accent;
  const dir = Math.abs(delta) < 0.1 ? "no change" : (delta > 0 ? "+" : "") + delta + " h/day";
  const fte = (total / 8).toFixed(1); // rough 8-hour-shift equivalents
  return (
    <div style={{ background: C.panel, border: "1px solid " + C.line, borderLeft: "3px solid " + C.accent, borderRadius: 6, padding: "10px 14px", fontSize: 13, fontFamily: "system-ui,sans-serif" }}>
      <div style={{ display: "flex", justifyContent: "space-between", alignItems: "baseline" }}>
        <span style={{ fontSize: 11, letterSpacing: ".06em", textTransform: "uppercase", color: C.sub }}>
          Staff time for basic care &middot; 15 min/animal/day
        </span>
        <span style={{ fontSize: 15, fontWeight: 700, color: col }}>
          {total.toFixed(1)} h/day <span style={{ fontSize: 12, fontWeight: 400, color: col }}>({dir})</span>
        </span>
      </div>
      <div style={{ marginTop: 5, color: C.sub }}>
        Cats <strong style={{ color: C.cat }}>{cat.staffHours} h</strong>
        <span style={{ margin: "0 8px", color: C.line }}>|</span>
        Dogs <strong style={{ color: C.dog }}>{dog.staffHours} h</strong>
        <span style={{ margin: "0 8px", color: C.line }}>|</span>
        ~{fte} staff at 8 h/day &middot; baseline {baseTotal.toFixed(1)} h/day
      </div>
    </div>
  );
}

// Trajectory (shown for coupling / breach cases): census with baseline ghost line.
function TrajectoryPanel({ res, ref, color, label }) {
  const s = res.summary;
  const ghost = ref.settledCensus;
  const data = res.series.slice(0, 90); // first 3 months; full year still drives the settle math
  return (
    <div style={{ background: C.paper, border: "1px solid " + C.line, borderRadius: 10, padding: 14 }}>
      <div style={{ display: "flex", justifyContent: "space-between", alignItems: "baseline", marginBottom: 8 }}>
        <h4 style={{ margin: 0, fontSize: 14.5 }}>{label}</h4>
        <span style={{ fontSize: 11.5, color: s.daysOverCFC > 0 ? C.warn : C.sub, fontFamily: "system-ui,sans-serif" }}>
          {s.daysOverCFC > 0 ? s.daysOverCFC + " days over C4C (full year)" : "within C4C"}
        </span>
      </div>
      <div style={{ height: 180 }}>
        <ResponsiveContainer>
          <ComposedChart data={data} margin={{ top: 6, right: 46, bottom: 2, left: -10 }}>
            <CartesianGrid stroke={C.line} vertical={false} />
            <ReferenceArea x1={1} x2={s.settleDays} fill={C.settle} fillOpacity={0.7}
              label={{ value: "settling", fontSize: 9, fill: C.sub, position: "insideTop" }} />
            <XAxis dataKey="day" tick={{ fontSize: 10.5, fill: C.sub }} tickLine={false} ticks={[15, 30, 45, 60, 75, 90]} domain={[1, 90]} type="number" />
            <YAxis tick={{ fontSize: 10.5, fill: C.sub }} tickLine={false} axisLine={false}
              domain={[0, Math.max(s.physicalMax + 10, s.finalCensus + 10)]} />
            <Tooltip contentStyle={{ fontSize: 12, borderRadius: 8, border: "1px solid " + C.line }} />
            <ReferenceLine y={ghost} stroke={C.sub} strokeDasharray="4 3"
              label={{ value: "baseline " + Math.round(ghost), position: "right", fontSize: 9.5, fill: C.sub }} />
            <ReferenceLine y={s.cfc} stroke={C.cfc} strokeDasharray="5 4"
              label={{ value: "C4C " + s.cfc, position: "right", fontSize: 10, fill: C.cfc }} />
            <ReferenceLine y={s.physicalMax} stroke={C.warn} strokeDasharray="2 3"
              label={{ value: "phys " + s.physicalMax, position: "right", fontSize: 10, fill: C.warn }} />
            <Area type="monotone" dataKey="census" stroke={color} fill={color} fillOpacity={0.12} strokeWidth={2} name="Census" dot={false} />
          </ComposedChart>
        </ResponsiveContainer>
      </div>
    </div>
  );
}


function Modal({ scenario, onClose }) {
  if (!scenario) return null;
  return (
    <div onClick={onClose} style={{ position: "fixed", inset: 0, background: "rgba(28,26,23,.45)", zIndex: 50, display: "flex", alignItems: "center", justifyContent: "center", padding: 20 }}>
      <div onClick={(e) => e.stopPropagation()} style={{ background: C.panel, borderRadius: 14, maxWidth: 520, padding: "26px 28px", boxShadow: "0 20px 60px rgba(0,0,0,.25)", fontFamily: "system-ui,sans-serif" }}>
        <div style={{ fontSize: 11, letterSpacing: ".14em", textTransform: "uppercase", color: C.accent, marginBottom: 6 }}>
          Scenario {scenario.name.split(".")[0]}{scenario.values ? " \u00b7 suggested values" : ""}
        </div>
        <h2 style={{ margin: "0 0 12px", fontSize: 22, fontFamily: "Georgia,serif", color: C.ink }}>{scenario.title}</h2>
        <p style={{ margin: "0 0 20px", fontSize: 14.5, lineHeight: 1.6, color: C.ink }}>{scenario.body}</p>
        <div style={{ fontSize: 12.5, color: C.sub, marginBottom: 18 }}>
          Set the levers on the left yourself, then press <strong>Run simulation</strong>.
        </div>
        <button onClick={onClose} style={{ background: C.ink, color: "#fff", border: "none", borderRadius: 8, padding: "9px 18px", fontSize: 13.5, cursor: "pointer" }}>Got it</button>
      </div>
    </div>
  );
}

export default function ShelterSim() {
  const [levers, setLevers] = useState({ ...DEFAULT_LEVERS });
  const [modal, setModal] = useState(null);
  const [methodsOpen, setMethodsOpen] = useState(false);
  const [result, setResult] = useState(null);
  const [origin, setOrigin] = useState("baseline");
  const [startStates, setStartStates] = useState(null);
  const reportDate = new Date().toISOString().slice(0, 10);

  const setLever = (k, v) => setLevers((p) => ({ ...p, [k]: v }));

  const runSimulation = useCallback(() => {
    const dogStart = startStates ? startStates.dog : seedState(BASE.dog);
    const catStart = startStates ? startStates.cat : seedState(BASE.cat);
    const dog = project(BASE.dog, levers, dogStart, PROJECTION_DAYS);
    const cat = project(BASE.cat, levers, catStart, PROJECTION_DAYS);
    setResult({ dog, cat });
    const priorDay = origin === "baseline" ? 0 : origin;
    setOrigin(priorDay + PROJECTION_DAYS);
    setStartStates({ dog: dog.endState, cat: cat.endState });
  }, [levers, startStates, origin]);

  const resetBaseline = useCallback(() => {
    setResult(null); setStartStates(null); setOrigin("baseline"); setLevers({ ...DEFAULT_LEVERS });
  }, []);

  const originLabel = origin === "baseline" ? "baseline" : "end of previous run (day " + origin + ")";

  const Lever = ({ label, hint, children }) => (
    <div style={{ marginBottom: 13 }}>
      <div style={{ fontSize: 12, fontWeight: 600, marginBottom: 4 }}>{label}</div>
      {children}
      {hint && <div style={{ fontSize: 11, color: C.sub, marginTop: 3 }}>{hint}</div>}
    </div>
  );

  return (
    <div style={{ fontFamily: "Georgia, serif", background: C.paper, color: C.ink, minHeight: "100vh" }}>
      <Modal scenario={modal} onClose={() => setModal(null)} />
      {methodsOpen && (
        <div onClick={() => setMethodsOpen(false)} style={{ position: "fixed", inset: 0, background: "rgba(28,26,23,.45)", zIndex: 50, display: "flex", alignItems: "center", justifyContent: "center", padding: 20 }}>
          <div onClick={(e) => e.stopPropagation()} style={{ background: C.panel, borderRadius: 14, maxWidth: 620, maxHeight: "80vh", overflowY: "auto", padding: "26px 28px", boxShadow: "0 20px 60px rgba(0,0,0,.25)", fontFamily: "system-ui,sans-serif" }}>
            <h2 style={{ margin: "0 0 12px", fontSize: 22, fontFamily: "Georgia,serif", color: C.ink }}>Methods</h2>
            <div style={{ fontSize: 13, color: C.ink, lineHeight: 1.65 }}>
              <p style={{ marginTop: 0 }}>Results compare the <strong>settled steady state</strong> (mean of the last 30 days of a 12-month projection) against baseline; a badge warns if a run hasn't settled by 12 months.</p>
              <p>LOS = outcome date &minus; intake date + 1; in-care animals are censored at the report date ({reportDate}). Baseline census is seeded across LOS bands so projections begin from a true steady state.</p>
              <p><strong>Doubling up</strong> closes portals/guillotines to house two animals per double unit, raising effective capacity toward the physical maximum. It drives a convex rise in respiratory disease prevalence (CIRD in dogs, feline URI in cats) from a baseline of 4% / 8% toward a ceiling near 38%, with low doubling relatively safe and high doubling steeply harmful.</p>
              <p>When the crowding cycle is on, disease above baseline lowers the adoption rate and lengthens adoption LOS, which raises census and density, which raises disease &mdash; a reinforcing loop. Independently and always on, two couplings make the outcome rates reflect crowding: euthanasia-for-space rises once occupancy exceeds C4C (steepening toward physical capacity), and respiratory disease above baseline adds to died-in-care and medical euthanasia. Because euthanasia-for-space also caps runaway census, a severe spiral settles at a high-euthanasia equilibrium rather than growing without bound.</p>
              <p><strong>Live Release Rate (SAC)</strong> = live outcomes (adoption + RTO + transfer-out + RTF) &divide; total outcomes. <strong>Save Rate</strong> = (intakes &minus; non-live outcomes) &divide; intakes, where non-live = euthanasia + died in care. <strong>Staff time for basic care</strong> assumes 15 minutes per in-shelter animal per day (foster animals excluded), summed across species and shown as hours per day.</p>
              <p>Trajectory charts show the first 3 months; the full 12-month projection still drives the settled steady-state values. All parameter mappings, including the disease model, are illustrative general-principle approximations, not shelter-specific or validated data. Identical inputs always produce identical output.</p>
            </div>
            <button onClick={() => setMethodsOpen(false)} style={{ marginTop: 8, background: C.ink, color: "#fff", border: "none", borderRadius: 8, padding: "9px 18px", fontSize: 13.5, cursor: "pointer" }}>Close</button>
          </div>
        </div>
      )}
      <div style={{ maxWidth: 1160, margin: "0 auto", padding: "26px 20px 60px" }}>

        <header style={{ borderBottom: "2px solid " + C.ink, paddingBottom: 14, marginBottom: 18 }}>
          <div style={{ fontSize: 11, letterSpacing: ".18em", textTransform: "uppercase", color: C.sub }}>
            Shelter Medicine &middot; Population Management
          </div>
          <h1 style={{ fontSize: 29, margin: "6px 0 4px", fontWeight: 700 }}>Population Management Simulation</h1>
          <div style={{ fontSize: 13, color: C.sub, fontFamily: "system-ui,sans-serif" }}>
            Deterministic teaching model &middot; 5,000 intake/yr suburban shelter &middot; report date {reportDate}
          </div>
        </header>

        <div style={{ display: "flex", flexWrap: "wrap", gap: 8, marginBottom: 18 }}>
          {SCENARIOS.map((s) => (
            <button key={s.key} onClick={() => setModal(s)} style={{ fontFamily: "system-ui,sans-serif", fontSize: 12.5, cursor: "pointer", padding: "7px 12px", borderRadius: 20, border: "1px solid " + C.line, background: C.panel, color: C.ink }}>{s.name}</button>
          ))}
        </div>

        <div style={{ display: "grid", gridTemplateColumns: "254px 1fr", gap: 20 }}>
          <aside style={{ alignSelf: "start", fontFamily: "system-ui,sans-serif" }}>
            <div style={{ background: C.panel, border: "1px solid " + C.line, borderRadius: 12, padding: 14, marginBottom: 14 }}>
              <div style={{ fontSize: 12, fontWeight: 700, marginBottom: 8 }}>Baseline state</div>
              <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 8 }}>
                <Stat label="Dogs census" value={BASE.dog.census} sub={"ALOS " + BASE.dog.alos + "d"} tone={C.dog} />
                <Stat label="Cats census" value={BASE.cat.census} sub={"ALOS " + BASE.cat.alos + "d"} tone={C.cat} />
              </div>
              <div style={{ fontSize: 11, color: C.sub, marginTop: 8 }}>Dogs C4C 183 (85% occ) &middot; Cats C4C 113 (85% occ)</div>
            </div>

            <div style={{ background: C.panel, border: "1px solid " + C.line, borderRadius: 12, padding: 14, marginBottom: 14 }}>
              <div style={{ fontSize: 12, fontWeight: 700, marginBottom: 4 }}>Levers</div>
              <div style={{ fontSize: 11, color: C.sub, marginBottom: 12 }}>Adjust, then Run. Changes apply only when you run.</div>

              <Lever label={"Dog intake: " + levers.intakeDog + "/day"} hint="Diversion / safety net lowers this">
                <input type="range" min="0" max="20" step="0.5" value={levers.intakeDog} onChange={(e) => setLever("intakeDog", +e.target.value)} style={{ width: "100%" }} />
              </Lever>
              <Lever label={"Cat intake: " + levers.intakeCat + "/day"} hint="Diversion / safety net lowers this">
                <input type="range" min="0" max="20" step="0.5" value={levers.intakeCat} onChange={(e) => setLever("intakeCat", +e.target.value)} style={{ width: "100%" }} />
              </Lever>
              <Lever label="Adoption barrier" hint="Low = shorter adoption LOS, higher adoption rate">
                <select value={levers.barrier} onChange={(e) => setLever("barrier", e.target.value)} style={{ width: "100%", padding: 6, borderRadius: 6, border: "1px solid " + C.line }}>
                  <option value="low">Low</option><option value="medium">Medium</option><option value="high">High</option>
                </select>
              </Lever>
              <Lever label={"Extra hold days: " + levers.holdExtraDays} hint="Medical/behavior holds extend LOS">
                <input type="range" min="0" max="20" step="1" value={levers.holdExtraDays} onChange={(e) => setLever("holdExtraDays", +e.target.value)} style={{ width: "100%" }} />
              </Lever>
              <Lever label={"Doubling up: " + Math.round(levers.doublingPct * 100) + "% of units"} hint="Close portals/guillotines: more space, more disease">
                <input type="range" min="0" max="1" step="0.05" value={levers.doublingPct} onChange={(e) => setLever("doublingPct", +e.target.value)} style={{ width: "100%" }} />
              </Lever>
              <Lever label={"Dog RTO outcomes as a % of stray intake: " + Math.round(levers.rtoStrayPct * 100) + "%"} hint="Dogs only. Most RTO outcomes occur within 2-3 days, contributing significantly to a lower ALOS.">
                <input type="range" min="0" max="0.6" step="0.01" value={levers.rtoStrayPct} onChange={(e) => setLever("rtoStrayPct", +e.target.value)} style={{ width: "100%" }} />
              </Lever>
              <Lever label={"RTF outcomes as a % of stray intake: " + Math.round(levers.rtfStrayPct * 100) + "%"} hint="Cats only; 3-day outcome pathway">
                <input type="range" min="0" max="0.6" step="0.01" value={levers.rtfStrayPct} onChange={(e) => setLever("rtfStrayPct", +e.target.value)} style={{ width: "100%" }} />
              </Lever>
              <Lever label={"Foster capacity: " + levers.fosterCapacity} hint="Diverts census, no outcome change">
                <input type="range" min="0" max="120" step="5" value={levers.fosterCapacity} onChange={(e) => setLever("fosterCapacity", +e.target.value)} style={{ width: "100%" }} />
              </Lever>
              <label style={{ display: "flex", alignItems: "center", gap: 8, fontSize: 13, cursor: "pointer", marginTop: 4 }}>
                <input type="checkbox" checked={levers.couplingOn} onChange={(e) => setLever("couplingOn", e.target.checked)} />
                Crowding vicious cycle
              </label>
              <div style={{ fontSize: 11, color: C.sub, marginTop: 4 }}>Doubling up / crowding raises disease, which cuts adoptions and lengthens stays, raising census</div>
            </div>

            <button onClick={runSimulation} style={{ width: "100%", background: C.accent, color: "#fff", border: "none", borderRadius: 9, padding: "12px", fontSize: 15, fontWeight: 700, cursor: "pointer", marginBottom: 8 }}>Run simulation</button>
            <button onClick={resetBaseline} style={{ width: "100%", background: C.panel, color: C.ink, border: "1px solid " + C.line, borderRadius: 9, padding: "10px", fontSize: 13.5, cursor: "pointer" }}>Reset to baseline</button>
          </aside>

          <main style={{ minWidth: 0 }}>
            <div style={{ background: C.panel, border: "1px solid " + C.line, borderLeft: "3px solid " + C.accent, borderRadius: 6, padding: "9px 14px", marginBottom: 16, fontSize: 13, fontFamily: "system-ui,sans-serif" }}>
              <strong>Projecting from:</strong> {originLabel}
            </div>

            {!result ? (
              <div style={{ background: C.paper, border: "1px dashed " + C.line, borderRadius: 12, padding: "60px 30px", textAlign: "center", color: C.sub, fontFamily: "system-ui,sans-serif" }}>
                <div style={{ fontSize: 16, marginBottom: 6 }}>No projection yet.</div>
                <div style={{ fontSize: 13.5 }}>Pick a scenario for guidance, set the levers, and press Run simulation. You'll see the resulting steady state compared against baseline.</div>
              </div>
            ) : (() => {
              // Show trajectories when dynamics matter: coupling on, or either species
              // crosses C4C at any point during the year.
              const dynamic = levers.couplingOn
                || result.dog.summary.peakOcc > 1.0 || result.cat.summary.peakOcc > 1.0
                || !result.dog.summary.settled || !result.cat.summary.settled;
              return (
                <div style={{ display: "grid", gap: 16 }}>
                  <div style={{ fontSize: 12.5, color: C.sub, fontFamily: "system-ui,sans-serif" }}>
                    Comparing the settled 12-month steady state (last 30-day average) against baseline.
                  </div>
                  <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 16 }}>
                    <SpeciesComparison label="Cats" color={C.cat} res={result.cat} ref={BASELINE_REF.cat} />
                    <SpeciesComparison label="Dogs" color={C.dog} res={result.dog} ref={BASELINE_REF.dog} />
                  </div>

                  <LrrDeltaNote dog={result.dog.summary} cat={result.cat.summary} refs={BASELINE_REF} />

                  <StaffTimePanel dog={result.dog.summary} cat={result.cat.summary} refs={BASELINE_REF} />

                  {dynamic && (
                    <div style={{ background: C.panel, border: "1px solid " + C.line, borderRadius: 12, padding: 16 }}>
                      <div style={{ fontSize: 13, fontWeight: 700, marginBottom: 4, fontFamily: "system-ui,sans-serif" }}>
                        Census Over Time
                      </div>
                      <div style={{ fontSize: 12, color: C.sub, marginBottom: 14, fontFamily: "system-ui,sans-serif" }}>
                        See how the daily census changes over time after the changes are made.
                      </div>
                      <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 16 }}>
                        <TrajectoryPanel res={result.cat} ref={BASELINE_REF.cat} color={C.cat} label="Cats" />
                        <TrajectoryPanel res={result.dog} ref={BASELINE_REF.dog} color={C.dog} label="Dogs" />
                      </div>
                    </div>
                  )}
                </div>
              );
            })()}

            <div style={{ borderTop: "1px solid " + C.line, paddingTop: 14, marginTop: 16 }}>
              <button onClick={() => setMethodsOpen(true)} style={{
                fontFamily: "system-ui,sans-serif", fontSize: 12.5, cursor: "pointer",
                padding: "8px 14px", borderRadius: 8, border: "1px solid " + C.line,
                background: C.panel, color: C.ink,
              }}>Learn more about methods</button>
            </div>
          </main>
        </div>
      </div>
    </div>
  );
}
export default App
