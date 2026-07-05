'use strict';

/* =====================================================================
   OS Process Scheduling Solver
   Engine  : pure scheduling algorithms (testable without a browser)
   Generator: random exam-style question builder
   UI      : DOM wiring (runs only in the browser)
   ===================================================================== */

/* ============================ ENGINE ============================ */
const Engine = (() => {

  // Default tie-breaker: earlier Arrival Time, then smaller input order (PID order)
  const TIE = (a, b) => a.at - b.at || a.idx - b.idx;

  function prep(procs) {
    return procs.map((p, i) => ({
      pid: String(p.pid),
      at: +p.at,
      bt: +p.bt,
      priority: (p.priority === '' || p.priority == null) ? null : +p.priority,
      io: (p.io === '' || p.io == null) ? 0 : +p.io,
      queue: (p.queue === '' || p.queue == null) ? 1 : +p.queue,
      idx: i,
      remaining: +p.bt,
      firstStart: null,
      ct: null
    }));
  }

  // Add a segment to the timeline, merging contiguous segments of the same pid
  function addSeg(tl, pid, start, end) {
    const last = tl[tl.length - 1];
    if (last && last.pid === pid && last.end === start) { last.end = end; return; }
    tl.push({ pid, start, end });
  }

  // Compute per-process stats + overall summary
  function finish(ps, tl, log) {
    const rows = ps.slice().sort((a, b) => a.idx - b.idx).map(p => {
      const tat = p.ct - p.at;                 // TAT = CT - AT
      const wt = tat - (p.bt + p.io);          // WT = TAT - (BT + I/O)
      const rt = p.firstStart - p.at;          // RT = first start - AT
      return { ...p, tat, wt, rt };
    });
    const lastCT = Math.max(...rows.map(r => r.ct));
    // Context switches: CPU changes directly from one process to a DIFFERENT process.
    // Idle -> process is not counted.
    let switches = 0;
    for (let i = 1; i < tl.length; i++) {
      const a = tl[i - 1], b = tl[i];
      if (a.pid !== 'Idle' && b.pid !== 'Idle' && a.pid !== b.pid) switches++;
    }
    const n = rows.length;
    const avg = k => rows.reduce((s, r) => s + r[k], 0) / n;
    const overhead = switches / lastCT;
    return {
      timeline: tl, rows, log,
      summary: {
        avgTAT: avg('tat'), avgWT: avg('wt'), avgRT: avg('rt'),
        throughput: n / lastCT,
        switches, overhead,
        efficiency: (1 - overhead) * 100,
        lastCT
      }
    };
  }

  /* ---------- FCFS (non-preemptive, criteria: AT) ---------- */
  function calculateFCFS(procs) {
    const ps = prep(procs);
    const order = ps.slice().sort(TIE);
    let t = 0; const tl = [], log = [];
    for (const p of order) {
      if (t < p.at) {
        addSeg(tl, 'Idle', t, p.at);
        log.push('Time ' + t + '\u2013' + p.at + ': CPU is idle (no process has arrived yet).');
        t = p.at;
      }
      p.firstStart = t;
      log.push('Time ' + t + ': ' + p.pid + ' has the earliest arrival (AT = ' + p.at + '), so FCFS runs it to completion (BT = ' + p.bt + ').');
      addSeg(tl, p.pid, t, t + p.bt);
      t += p.bt; p.ct = t;
    }
    return finish(ps, tl, log);
  }

  /* ---------- Generic non-preemptive scheduler ---------- */
  function nonPreemptive(procs, pick, reason) {
    const ps = prep(procs);
    let t = 0, done = 0; const tl = [], log = [];
    while (done < ps.length) {
      const ready = ps.filter(p => p.ct === null && p.at <= t);
      if (!ready.length) {
        const next = Math.min(...ps.filter(p => p.ct === null).map(p => p.at));
        addSeg(tl, 'Idle', t, next);
        log.push('Time ' + t + '\u2013' + next + ': CPU is idle (no process has arrived yet).');
        t = next; continue;
      }
      const p = pick(ready);
      p.firstStart = t;
      log.push(reason(t, p, ready));
      addSeg(tl, p.pid, t, t + p.bt);
      t += p.bt; p.ct = t; done++;
    }
    return finish(ps, tl, log);
  }

  /* ---------- SJF (non-preemptive, criteria: BT) ---------- */
  const calculateSJF = procs => nonPreemptive(
    procs,
    ready => ready.slice().sort((a, b) => a.bt - b.bt || TIE(a, b))[0],
    (t, p, ready) => 'Time ' + t + ': ready = [' + ready.map(r => r.pid + '(BT=' + r.bt + ')').join(', ') + ']. ' +
      p.pid + ' has the shortest burst time, so SJF runs it to completion.'
  );

  /* ---------- Priority non-preemptive ---------- */
  const calculatePriorityNP = (procs, rule) => nonPreemptive(
    procs,
    ready => ready.slice().sort((a, b) =>
      (rule === 'high' ? b.priority - a.priority : a.priority - b.priority) || TIE(a, b))[0],
    (t, p, ready) => 'Time ' + t + ': ready = [' + ready.map(r => r.pid + '(Pr=' + r.priority + ')').join(', ') + ']. ' +
      p.pid + ' has the best priority (' + (rule === 'high' ? 'highest' : 'lowest') + ' number wins), so it runs to completion.'
  );

  /* ---------- Generic preemptive unit-time scheduler ---------- */
  function preemptiveUnit(procs, pick, describe) {
    const ps = prep(procs);
    let t = 0, done = 0, running = null;
    const tl = [], log = [];
    while (done < ps.length) {
      const ready = ps.filter(p => p.ct === null && p.at <= t);
      if (!ready.length) { addSeg(tl, 'Idle', t, t + 1); running = null; t++; continue; }
      const p = pick(ready, t);
      if (p.firstStart === null) p.firstStart = t;
      if (running !== p.pid) log.push(describe(t, p, ready, running));
      addSeg(tl, p.pid, t, t + 1);
      p.remaining--; t++;
      if (p.remaining === 0) { p.ct = t; done++; running = null; }
      else running = p.pid;
    }
    return finish(ps, tl, log);
  }

  /* ---------- SRTF (preemptive SJF) ---------- */
  const calculateSRTF = procs => preemptiveUnit(
    procs,
    ready => ready.slice().sort((a, b) => a.remaining - b.remaining || TIE(a, b))[0],
    (t, p, ready, prev) => prev
      ? 'Time ' + t + ': ' + p.pid + ' (remaining = ' + p.remaining + ') replaces ' + prev + ' \u2014 shortest remaining time wins.'
      : 'Time ' + t + ': ' + p.pid + ' selected \u2014 shortest remaining time (' + p.remaining + ') among ready processes.'
  );

  /* ---------- Priority preemptive (optional aging) ---------- */
  const calculatePriorityP = (procs, rule, agingEvery) => preemptiveUnit(
    procs,
    (ready, t) => {
      const eff = p => {
        let pr = p.priority;
        if (agingEvery > 0) {
          const boost = Math.floor((t - p.at) / agingEvery);
          pr = rule === 'high' ? pr + boost : pr - boost;
        }
        return pr;
      };
      return ready.slice().sort((a, b) =>
        (rule === 'high' ? eff(b) - eff(a) : eff(a) - eff(b)) || TIE(a, b))[0];
    },
    (t, p, ready, prev) => prev
      ? 'Time ' + t + ': ' + p.pid + ' (priority ' + p.priority + ') preempts ' + prev + ' \u2014 better priority.'
      : 'Time ' + t + ': ' + p.pid + ' selected \u2014 best priority (' + p.priority + ') among ready processes.'
  );

  /* ---------- Round Robin ---------- */
  function calculateRR(procs, qt) {
    qt = +qt;
    const ps = prep(procs);
    const arrival = ps.slice().sort(TIE);
    let t = 0, ai = 0, done = 0;
    const q = [], tl = [], log = [];
    const enq = () => { while (ai < arrival.length && arrival[ai].at <= t) q.push(arrival[ai++]); };
    enq();
    while (done < ps.length) {
      if (!q.length) {
        const nt = arrival[ai].at;
        addSeg(tl, 'Idle', t, nt);
        log.push('Time ' + t + '\u2013' + nt + ': CPU is idle \u2014 ready queue is empty.');
        t = nt; enq(); continue;
      }
      const p = q.shift();
      if (p.firstStart === null) p.firstStart = t;
      const run = Math.min(qt, p.remaining);
      addSeg(tl, p.pid, t, t + run);
      t += run; p.remaining -= run;
      enq(); // arrivals during the slice join the queue BEFORE the preempted process
      if (p.remaining > 0) {
        q.push(p);
        log.push('Time ' + (t - run) + '\u2013' + t + ': ' + p.pid + ' runs one quantum (QT = ' + qt + '), remaining = ' + p.remaining + ', so it goes to the back of the queue.');
      } else {
        p.ct = t; done++;
        log.push('Time ' + (t - run) + '\u2013' + t + ': ' + p.pid + ' runs ' + run + ' unit(s) and finishes (CT = ' + t + ').');
      }
    }
    return finish(ps, tl, log);
  }

  /* ---------- Multi-Level Queue ----------
     levels: [{algo:'fcfs'|'sjf'|'srtf'|'rr'|'priority', qt?, rule?}] (index 0 = queue 1 = top priority)
     Each process has p.queue (1-based). Higher queue (smaller number) preempts lower queues.
     FCFS/SJF: non-preemptive inside their queue. SRTF/Priority: re-evaluated each unit. RR: per-queue quantum. */
  function calculateMLQ(procs, levels) {
    const ps = prep(procs);
    let t = 0, done = 0, running = null, qUsed = 0;
    const tl = [], log = [];
    const rrOrders = levels.map(() => []);
    const enqueued = new Set();

    while (done < ps.length) {
      for (const p of ps) {
        if (p.ct === null && p.at <= t && !enqueued.has(p.idx)) {
          enqueued.add(p.idx);
          rrOrders[p.queue - 1].push(p);
        }
      }
      const ready = ps.filter(p => p.ct === null && p.at <= t);
      if (!ready.length) { addSeg(tl, 'Idle', t, t + 1); t++; running = null; qUsed = 0; continue; }

      const lvl = Math.min(...ready.map(p => p.queue));
      const cfg = levels[lvl - 1];
      let p = null;

      // Can the running process continue?
      if (running && running.ct === null && running.queue === lvl) {
        if (cfg.algo === 'fcfs' || cfg.algo === 'sjf') p = running;              // non-preemptive inside queue
        else if (cfg.algo === 'rr' && qUsed < cfg.qt) p = running;               // quantum not finished
      }

      if (!p) {
        const cand = ready.filter(x => x.queue === lvl);
        if (cfg.algo === 'fcfs') p = cand.slice().sort(TIE)[0];
        else if (cfg.algo === 'sjf') p = cand.slice().sort((a, b) => a.bt - b.bt || TIE(a, b))[0];
        else if (cfg.algo === 'srtf') p = cand.slice().sort((a, b) => a.remaining - b.remaining || TIE(a, b))[0];
        else if (cfg.algo === 'priority') {
          const rule = cfg.rule || 'low';
          p = cand.slice().sort((a, b) =>
            (rule === 'high' ? b.priority - a.priority : a.priority - b.priority) || TIE(a, b))[0];
        } else if (cfg.algo === 'rr') {
          const arr = rrOrders[lvl - 1];
          if (running && running.queue === lvl && running.ct === null && qUsed >= cfg.qt) {
            const i = arr.indexOf(running);
            if (i > -1) { arr.splice(i, 1); arr.push(running); }
          }
          p = arr.filter(x => x.ct === null && x.at <= t)[0];
        }
        qUsed = 0;
      }

      if (p.firstStart === null) p.firstStart = t;
      if (!running || running.pid !== p.pid) {
        log.push('Time ' + t + ': Queue ' + lvl + ' (' + cfg.algo.toUpperCase() + (cfg.algo === 'rr' ? ', QT=' + cfg.qt : '') + ') is the highest non-empty queue \u2192 selects ' + p.pid + (running ? ' (replacing ' + running.pid + ')' : '') + '.');
      }
      qUsed = (running && running.pid === p.pid) ? qUsed + 1 : 1;
      addSeg(tl, p.pid, t, t + 1);
      p.remaining--; t++;
      if (p.remaining === 0) { p.ct = t; done++; running = null; qUsed = 0; }
      else running = p;
    }
    return finish(ps, tl, log);
  }

  /* ---------- Dispatcher ---------- */
  function run(algo, procs, opts) {
    opts = opts || {};
    switch (algo) {
      case 'fcfs': return calculateFCFS(procs);
      case 'sjf': return calculateSJF(procs);
      case 'srtf': return calculateSRTF(procs);
      case 'rr': return calculateRR(procs, opts.qt);
      case 'priority-np': return calculatePriorityNP(procs, opts.rule || 'low');
      case 'priority-p': return calculatePriorityP(procs, opts.rule || 'low', opts.aging || 0);
      case 'mlq': return calculateMLQ(procs, opts.levels);
      default: throw new Error('Unknown algorithm: ' + algo);
    }
  }

  return { calculateFCFS, calculateSJF, calculateSRTF, calculateRR, calculatePriorityNP, calculatePriorityP, calculateMLQ, run };
})();

/* ============================ GENERATOR ============================ */
const Generator = (() => {
  const ri = (a, b) => a + Math.floor(Math.random() * (b - a + 1));
  const pick = arr => arr[ri(0, arr.length - 1)];

  const NAMES = {
    'fcfs': 'FCFS (First Come First Serve, non-preemptive)',
    'sjf': 'SJF (Shortest Job First, non-preemptive)',
    'srtf': 'SRTF (Shortest Remaining Time First, preemptive)',
    'rr': 'Round Robin (preemptive)',
    'priority-np': 'Priority Scheduling (non-preemptive)',
    'priority-p': 'Priority Scheduling (preemptive)',
    'mlq': 'Multi-Level Queue'
  };

  function generateProcesses(s, usePriority, useQueue) {
    const procs = [];
    for (let i = 0; i < s.n; i++) {
      procs.push({
        pid: 'P' + (i + 1),
        at: ri(0, Math.max(0, s.atMax)),
        bt: ri(s.btMin, s.btMax),
        priority: usePriority ? ri(1, Math.max(4, s.n)) : '',
        io: s.includeIO ? ri(0, 2) : 0,
        queue: useQueue ? ri(1, 2) : 1
      });
    }
    // Guarantee something arrives reasonably early
    procs[0].at = Math.min(procs[0].at, 1);

    // Difficulty adjustments ("professor tricks")
    if (s.diff === 'easy') {
      procs.forEach((p, i) => { p.at = Math.min(p.at, i * 2); p.io = 0; });
    }
    if (s.diff === 'hard' || s.diff === 'tricky') {
      if (s.n >= 2) procs[1].at = procs[0].at;                 // arrival tie
    }
    if (s.diff === 'tricky') {
      if (s.n >= 3) procs[2].bt = procs[1].bt;                 // equal burst times
      if (usePriority && s.n >= 4) procs[3].priority = procs[0].priority; // equal priorities
      const maxAT = Math.max(...procs.slice(0, s.n - 1).map(p => p.at));
      procs[s.n - 1].at = maxAT + ri(3, 6);                    // possible CPU idle gap
    }
    return procs;
  }

  function generateQuestion(s) {
    const algo = s.algo === 'mixed'
      ? pick(['fcfs', 'sjf', 'srtf', 'rr', 'priority-np', 'priority-p'])
      : s.algo;
    const usePriority = algo === 'priority-np' || algo === 'priority-p';
    const rule = s.rule === 'random' ? pick(['low', 'high']) : s.rule;
    const qt = algo === 'rr' ? (s.qtMode === 'fixed' ? +s.qt : ri(2, 4)) : null;

    let mlq = null;
    const procs = generateProcesses(s, usePriority, algo === 'mlq');
    if (algo === 'mlq') {
      mlq = { levels: [{ algo: 'rr', qt: ri(2, 3) }, { algo: 'fcfs' }] };
      procs.forEach(p => { p.queue = ri(1, 2); });
      procs[0].queue = 1; // make sure queue 1 is used
    }

    let statement = 'Consider the following ' + s.n + ' processes. Using ' + NAMES[algo] + ' scheduling';
    if (algo === 'rr') statement += ' with Quantum Time QT = ' + qt;
    if (usePriority) statement += ', where the ' + (rule === 'high' ? 'HIGHEST' : 'LOWEST') + ' priority number means higher priority';
    if (algo === 'mlq') statement += '. Queue 1 (highest priority) uses Round Robin with QT = ' + mlq.levels[0].qt + ', and Queue 2 uses FCFS. A process in Queue 1 preempts Queue 2';
    statement += ', draw the Gantt chart and compute CT, TAT, WT and RT for every process, then find the average TAT / WT / RT, throughput, number of context switches, overhead and CPU efficiency.';
    if (s.includeIO) statement += ' Note: I/O time is given for each process, and WT = TAT \u2212 (BT + I/O).';

    return { algo, rule, qt, mlq, procs, statement, usePriority, includeIO: s.includeIO, algoName: NAMES[algo] };
  }

  return { generateQuestion };
})();

/* Export for Node.js tests */
if (typeof module !== 'undefined' && module.exports) {
  module.exports = { Engine, Generator };
}

/* ============================ UI ============================ */
if (typeof document !== 'undefined') (function () {

  const $ = id => document.getElementById(id);
  const fmt = x => Number.isInteger(x) ? String(x) : (+x.toFixed(3)).toString();

  const PALETTE = ['#5E9FE8', '#EAC26B', '#72BC8F', '#BF8EDA', '#DE9255', '#DF84A8', '#4FB9C9', '#E97366'];
  const ALGO_LABEL = {
    'fcfs': 'FCFS', 'sjf': 'SJF', 'srtf': 'SRTF', 'rr': 'Round Robin',
    'priority-np': 'Priority (Non-Preemptive)', 'priority-p': 'Priority (Preemptive)', 'mlq': 'Multi-Level Queue'
  };

  /* ---------- View switching ---------- */
  function switchView(name) {
    document.querySelectorAll('.view').forEach(v => { v.hidden = v.id !== 'view-' + name; });
    document.querySelectorAll('.nav-btn').forEach(b => b.classList.toggle('active', b.dataset.view === name));
    window.scrollTo({ top: 0 });
  }
  document.querySelectorAll('.nav-btn').forEach(b => b.addEventListener('click', () => switchView(b.dataset.view)));
  document.querySelectorAll('.mode-card').forEach(c => c.addEventListener('click', () => switchView(c.dataset.goto)));

  /* ---------- Solver: options visibility ---------- */
  function currentAlgo() { return $('algo').value; }

  function updateOptions() {
    const a = currentAlgo();
    const isPriority = a === 'priority-np' || a === 'priority-p';
    $('opt-qt').hidden = a !== 'rr';
    $('opt-rule').hidden = !(isPriority || a === 'mlq');
    $('opt-aging').hidden = a !== 'priority-p';
    $('mlq-config').hidden = a !== 'mlq';
    const needPriorityCol = isPriority || a === 'mlq';
    document.querySelectorAll('.col-priority').forEach(el => el.classList.toggle('hide', !needPriorityCol));
    document.querySelectorAll('.col-queue').forEach(el => el.classList.toggle('hide', a !== 'mlq'));
    if (a === 'mlq') buildMLQRows();
  }
  $('algo').addEventListener('change', updateOptions);

  /* ---------- MLQ config rows ---------- */
  function buildMLQRows() {
    const n = Math.min(4, Math.max(2, +$('mlq-levels').value || 2));
    $('mlq-levels').value = n;
    const host = $('mlq-rows');
    const prev = collectMLQLevels(true);
    host.innerHTML = '';
    for (let i = 0; i < n; i++) {
      const row = document.createElement('div');
      row.className = 'mlq-row';
      row.innerHTML =
        '<div class="lvl">Queue ' + (i + 1) + (i === 0 ? ' \u2b50' : '') + '</div>' +
        '<label>Algorithm <select class="mlq-algo">' +
        '<option value="fcfs">FCFS</option><option value="sjf">SJF</option>' +
        '<option value="srtf">SRTF</option><option value="rr">Round Robin</option>' +
        '<option value="priority">Priority</option></select></label>' +
        '<label class="mlq-qt-wrap">Quantum (RR only) <input type="number" class="mlq-qt" min="1" value="2"></label>';
      host.appendChild(row);
      if (prev[i]) {
        row.querySelector('.mlq-algo').value = prev[i].algo;
        if (prev[i].qt) row.querySelector('.mlq-qt').value = prev[i].qt;
      }
    }
  }
  $('mlq-levels').addEventListener('change', buildMLQRows);

  function collectMLQLevels(silent) {
    const rows = document.querySelectorAll('#mlq-rows .mlq-row');
    const levels = [];
    rows.forEach(r => {
      levels.push({
        algo: r.querySelector('.mlq-algo').value,
        qt: +r.querySelector('.mlq-qt').value || 2,
        rule: $('rule').value
      });
    });
    return levels;
  }

  /* ---------- Solver: process table ---------- */
  let rowCount = 0;
  function addRow(p) {
    p = p || {};
    rowCount++;
    const tr = document.createElement('tr');
    tr.innerHTML =
      '<td><input class="pid-in" type="text" value="' + (p.pid || 'P' + rowCount) + '" aria-label="PID"></td>' +
      '<td><input class="at-in" type="number" min="0" value="' + (p.at != null ? p.at : 0) + '" aria-label="Arrival time"></td>' +
      '<td><input class="bt-in" type="number" min="1" value="' + (p.bt != null ? p.bt : 1) + '" aria-label="Burst time"></td>' +
      '<td class="col-priority' + (document.querySelector('th.col-priority').classList.contains('hide') ? ' hide' : '') + '"><input class="pr-in" type="number" value="' + (p.priority != null ? p.priority : 1) + '" aria-label="Priority"></td>' +
      '<td><input class="io-in" type="number" min="0" value="' + (p.io != null ? p.io : 0) + '" aria-label="IO time"></td>' +
      '<td class="col-queue' + (document.querySelector('th.col-queue').classList.contains('hide') ? ' hide' : '') + '"><input class="q-in" type="number" min="1" value="' + (p.queue != null ? p.queue : 1) + '" aria-label="Queue level"></td>' +
      '<td><button class="btn ghost danger small" type="button">Remove</button></td>';
    tr.querySelector('button').addEventListener('click', () => tr.remove());
    $('pbody').appendChild(tr);
  }

  function resetTable() {
    $('pbody').innerHTML = '';
    rowCount = 0;
    $('solver-error').hidden = true;
    $('solver-results').innerHTML = '';
  }

  function loadSample() {
    resetTable();
    [{ pid: 'P1', at: 0, bt: 5, priority: 2, io: 0 },
     { pid: 'P2', at: 1, bt: 3, priority: 1, io: 0 },
     { pid: 'P3', at: 2, bt: 8, priority: 3, io: 0 },
     { pid: 'P4', at: 3, bt: 6, priority: 2, io: 0 }].forEach(addRow);
    $('qt').value = 2;
  }

  function collectProcesses() {
    const algo = currentAlgo();
    const needPriority = algo === 'priority-np' || algo === 'priority-p' ||
      (algo === 'mlq' && collectMLQLevels().some(l => l.algo === 'priority'));
    const rows = document.querySelectorAll('#pbody tr');
    const errors = [], procs = [], seen = new Set();
    if (!rows.length) errors.push('Add at least one process.');
    rows.forEach((r, i) => {
      const pid = r.querySelector('.pid-in').value.trim() || ('P' + (i + 1));
      const at = r.querySelector('.at-in').value;
      const bt = r.querySelector('.bt-in').value;
      const pr = r.querySelector('.pr-in').value;
      const io = r.querySelector('.io-in').value;
      const qu = r.querySelector('.q-in').value;
      if (seen.has(pid)) errors.push('Duplicate PID "' + pid + '" \u2014 PIDs must be unique.');
      seen.add(pid);
      if (at === '' || isNaN(+at) || +at < 0) errors.push(pid + ': Arrival Time must be a number \u2265 0.');
      if (bt === '' || isNaN(+bt) || +bt <= 0) errors.push(pid + ': Burst Time must be a number > 0.');
      if (io === '' || isNaN(+io) || +io < 0) errors.push(pid + ': I/O Time must be a number \u2265 0.');
      if (needPriority && (pr === '' || isNaN(+pr))) errors.push(pid + ': Priority must be numeric for this algorithm.');
      if (algo === 'mlq') {
        const levels = collectMLQLevels().length;
        if (qu === '' || isNaN(+qu) || +qu < 1 || +qu > levels) errors.push(pid + ': Queue must be between 1 and ' + levels + '.');
      }
      procs.push({ pid, at: +at, bt: +bt, priority: pr === '' ? null : +pr, io: +io || 0, queue: +qu || 1 });
    });
    if (algo === 'rr' && (!$('qt').value || +$('qt').value <= 0)) errors.push('Quantum Time must be a number > 0 for Round Robin.');
    return { procs, errors };
  }

  /* ---------- Rendering ---------- */
  function colorMap(timeline) {
    const map = {}; let i = 0;
    timeline.forEach(s => {
      if (s.pid !== 'Idle' && !(s.pid in map)) { map[s.pid] = PALETTE[i % PALETTE.length]; i++; }
    });
    return map;
  }

  function ganttHTML(timeline) {
    const total = timeline[timeline.length - 1].end;
    const start = timeline[0].start;
    const span = total - start;
    const colors = colorMap(timeline);
    let html = '<div class="gantt-track">';
    timeline.forEach((s, i) => {
      const w = Math.max(4, (s.end - s.start) / span * 100);
      const idle = s.pid === 'Idle';
      html += '<div class="g-block' + (idle ? ' idle' : '') + '" style="flex-grow:' + (s.end - s.start) +
        ';' + (idle ? '' : 'background:' + colors[s.pid] + ';') + '" title="' + s.pid + ': ' + s.start + '\u2013' + s.end + '">' +
        '<span>' + s.pid + '</span><span class="g-t">' + s.start + '</span>' +
        (i === timeline.length - 1 ? '<span class="g-tend">' + s.end + '</span>' : '') +
        '</div>';
    });
    html += '</div>';
    return html;
  }

  function renderResults(container, res, meta) {
    const s = res.summary;
    const showPriority = res.rows.some(r => r.priority != null);
    const showQueue = meta.algo === 'mlq';
    const showIO = res.rows.some(r => r.io > 0);

    let table = '<div class="table-wrap"><table><thead><tr>' +
      '<th>PID</th><th>AT</th><th>BT</th>' +
      (showPriority ? '<th>Priority</th>' : '') +
      (showQueue ? '<th>Queue</th>' : '') +
      (showIO ? '<th>I/O</th>' : '') +
      '<th>First Start</th><th>CT</th><th>TAT</th><th>WT</th><th>RT</th></tr></thead><tbody>';
    res.rows.forEach(r => {
      table += '<tr><td><b>' + r.pid + '</b></td><td>' + r.at + '</td><td>' + r.bt + '</td>' +
        (showPriority ? '<td>' + (r.priority != null ? r.priority : '\u2014') + '</td>' : '') +
        (showQueue ? '<td>' + r.queue + '</td>' : '') +
        (showIO ? '<td>' + r.io + '</td>' : '') +
        '<td>' + r.firstStart + '</td><td>' + r.ct + '</td><td>' + r.tat + '</td><td>' + r.wt + '</td><td>' + r.rt + '</td></tr>';
    });
    table += '</tbody></table></div>';

    const cards = [
      ['Avg TAT', fmt(s.avgTAT)], ['Avg WT', fmt(s.avgWT)], ['Avg RT', fmt(s.avgRT)],
      ['Throughput', fmt(s.throughput) + ' /unit'], ['Context switches', s.switches],
      ['Overhead', fmt(s.overhead)], ['Efficiency', fmt(s.efficiency) + '%'], ['Last CT', s.lastCT]
    ].map(c => '<div class="sum-card"><b>' + c[1] + '</b><span>' + c[0] + '</span></div>').join('');

    container.innerHTML =
      '<div class="card results-card">' +
      '<div class="q-head"><h3>Solution \u2014 ' + meta.label + '</h3>' +
      '<button class="btn ghost" type="button" onclick="window.print()">Print / Export</button></div>' +
      (meta.note ? '<p class="hint">' + meta.note + '</p>' : '') +
      '<h4>Gantt chart</h4>' + ganttHTML(res.timeline) +
      '<h4>Results table</h4>' + table +
      '<h4>Summary</h4><div class="summary-grid">' + cards + '</div>' +
      '<h4>Step-by-step explanation</h4><ol class="steps">' +
      res.log.map(l => '<li>' + l + '</li>').join('') + '</ol>' +
      '</div>';
    container.scrollIntoView({ behavior: 'smooth', block: 'start' });
  }

  /* ---------- Solver: calculate ---------- */
  function onCalculate() {
    const { procs, errors } = collectProcesses();
    const errBox = $('solver-error');
    if (errors.length) {
      errBox.innerHTML = errors.join('<br>');
      errBox.hidden = false;
      $('solver-results').innerHTML = '';
      return;
    }
    errBox.hidden = true;
    const algo = currentAlgo();
    const opts = {
      qt: +$('qt').value,
      rule: $('rule').value,
      aging: +$('aging').value || 0,
      levels: collectMLQLevels()
    };
    let note = '';
    if (algo === 'rr') note = 'Quantum Time QT = ' + opts.qt + '.';
    if (algo === 'priority-np' || algo === 'priority-p') {
      note = (opts.rule === 'high' ? 'Highest' : 'Lowest') + ' priority number wins.' +
        (algo === 'priority-p' && opts.aging > 0 ? ' Aging: priority improves every ' + opts.aging + ' waiting units.' : '');
    }
    if (algo === 'mlq') note = 'Queue 1 is the highest priority queue. ' + opts.levels.map((l, i) => 'Queue ' + (i + 1) + ' = ' + l.algo.toUpperCase() + (l.algo === 'rr' ? ' (QT=' + l.qt + ')' : '')).join(' \u00b7 ');
    try {
      const res = Engine.run(algo, procs, opts);
      renderResults($('solver-results'), res, { label: ALGO_LABEL[algo], note, algo });
    } catch (e) {
      errBox.textContent = 'Error: ' + e.message;
      errBox.hidden = false;
    }
  }

  $('btn-add').addEventListener('click', () => addRow());
  $('btn-sample').addEventListener('click', loadSample);
  $('btn-reset').addEventListener('click', resetTable);
  $('btn-calc').addEventListener('click', onCalculate);

  /* ---------- Practice generator ---------- */
  let currentQ = null, solutionShown = false;

  $('g-qtmode').addEventListener('change', () => { $('g-qt-wrap').hidden = $('g-qtmode').value !== 'fixed'; });

  function collectSettings() {
    const btMin = Math.max(1, +$('g-btmin').value || 1);
    const btMax = Math.max(btMin, +$('g-btmax').value || btMin);
    return {
      algo: $('g-algo').value,
      n: Math.min(8, Math.max(3, +$('g-n').value || 4)),
      atMax: Math.max(0, +$('g-atmax').value || 0),
      btMin, btMax,
      includeIO: $('g-io').value === 'yes',
      rule: $('g-rule').value,
      qtMode: $('g-qtmode').value,
      qt: Math.max(1, +$('g-qt').value || 2),
      diff: $('g-diff').value
    };
  }

  function questionTableHTML(q) {
    let html = '<thead><tr><th>PID</th><th>AT</th><th>BT</th>' +
      (q.usePriority ? '<th>Priority</th>' : '') +
      (q.includeIO ? '<th>I/O</th>' : '') +
      (q.algo === 'mlq' ? '<th>Queue</th>' : '') + '</tr></thead><tbody>';
    q.procs.forEach(p => {
      html += '<tr><td><b>' + p.pid + '</b></td><td>' + p.at + '</td><td>' + p.bt + '</td>' +
        (q.usePriority ? '<td>' + p.priority + '</td>' : '') +
        (q.includeIO ? '<td>' + p.io + '</td>' : '') +
        (q.algo === 'mlq' ? '<td>' + p.queue + '</td>' : '') + '</tr>';
    });
    return html + '</tbody>';
  }

  function generate() {
    currentQ = Generator.generateQuestion(collectSettings());
    solutionShown = false;
    $('question-card').hidden = false;
    $('q-algo-pill').textContent = ALGO_LABEL[currentQ.algo];
    $('q-statement').textContent = currentQ.statement;
    $('q-table').innerHTML = questionTableHTML(currentQ);
    $('btn-reveal').textContent = 'Reveal solution';
    $('practice-results').innerHTML = '';
    $('question-card').scrollIntoView({ behavior: 'smooth', block: 'start' });
  }

  function reveal() {
    if (!currentQ) return;
    if (solutionShown) {
      $('practice-results').innerHTML = '';
      $('btn-reveal').textContent = 'Reveal solution';
      solutionShown = false;
      return;
    }
    const opts = {
      qt: currentQ.qt,
      rule: currentQ.rule,
      aging: 0,
      levels: currentQ.mlq ? currentQ.mlq.levels : null
    };
    let note = '';
    if (currentQ.algo === 'rr') note = 'Quantum Time QT = ' + currentQ.qt + '.';
    if (currentQ.usePriority) note = (currentQ.rule === 'high' ? 'Highest' : 'Lowest') + ' priority number wins.';
    if (currentQ.algo === 'mlq') note = 'Queue 1 = RR (QT=' + currentQ.mlq.levels[0].qt + '), Queue 2 = FCFS. Queue 1 preempts Queue 2.';
    const res = Engine.run(currentQ.algo, currentQ.procs, opts);
    renderResults($('practice-results'), res, { label: currentQ.algoName, note, algo: currentQ.algo });
    $('btn-reveal').textContent = 'Hide solution';
    solutionShown = true;
  }

  $('btn-generate').addEventListener('click', generate);
  $('btn-newq').addEventListener('click', generate);
  $('btn-reveal').addEventListener('click', reveal);

  /* ---------- Init ---------- */
  updateOptions();
  loadSample();

  // Demo hook for quick preview: opens solver with sample data already calculated
  if (location.hash === '#demo') {
    switchView('solver');
    onCalculate();
  } else if (location.hash === '#demo-practice') {
    switchView('practice');
    generate();
    reveal();
  }
})();
