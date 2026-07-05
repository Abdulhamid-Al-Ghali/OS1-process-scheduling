'use strict';

/* =====================================================================
   OS-1 Process Scheduling Solver
   Engine   : pure scheduling algorithms (testable without a browser)
   Generator: random exam-style question builder
   UI       : DOM wiring (runs only in the browser)

   Multi-burst support:
   A process may have a burst sequence like "5, I3, 4, I2, 6"
   = CPU 5 -> I/O 3 -> CPU 4 -> I/O 2 -> CPU 6.
   While a process is doing I/O it is blocked (never shown on the CPU);
   it rejoins the ready queue when its I/O finishes.
   CT = the time when the FINAL CPU burst finishes.
   ===================================================================== */

/* ============================ ENGINE ============================ */
const Engine = (() => {

  // Default tie-breaker: earlier Arrival Time, then smaller input (PID) order
  const TIE = (a, b) => a.at - b.at || a.idx - b.idx;
  const LIMIT = 200000; // simulation safety cap

  /* parseBurstSequence("5, I3, 4") ->
     [{type:'cpu',len:5},{type:'io',len:3},{type:'cpu',len:4}]
     Rules: starts with CPU, ends with CPU, CPU > 0, I/O >= 0, alternating. */
  function parseBurstSequence(text) {
    const parts = String(text).split(',').map(s => s.trim()).filter(s => s !== '');
    if (!parts.length) throw new Error('Burst sequence is empty.');
    const seq = [];
    for (const raw of parts) {
      const isIO = /^i/i.test(raw);
      const numStr = isIO ? raw.replace(/^i\s*\/?\s*o?\s*/i, '') : raw;
      const val = Number(numStr);
      if (numStr === '' || !isFinite(val)) throw new Error('Invalid burst entry "' + raw + '".');
      if (isIO) {
        if (val < 0) throw new Error('I/O bursts must be \u2265 0 ("' + raw + '").');
        seq.push({ type: 'io', len: val });
      } else {
        if (val <= 0) throw new Error('CPU bursts must be > 0 ("' + raw + '").');
        seq.push({ type: 'cpu', len: val });
      }
    }
    if (seq[0].type !== 'cpu') throw new Error('A burst sequence must start with a CPU burst.');
    if (seq[seq.length - 1].type !== 'cpu') throw new Error('A burst sequence must end with a CPU burst.');
    for (let i = 1; i < seq.length; i++)
      if (seq[i].type === seq[i - 1].type)
        throw new Error('CPU and I/O bursts must alternate in the sequence.');
    return seq;
  }

  const calculateTotalBT = seq => seq.filter(b => b.type === 'cpu').reduce((s, b) => s + b.len, 0);
  const calculateTotalIO = seq => seq.filter(b => b.type === 'io').reduce((s, b) => s + b.len, 0);
  const seqText = seq => seq.map(b => (b.type === 'io' ? 'I' + b.len : String(b.len))).join(', ');

  function prep(procs) {
    return procs.map((p, i) => {
      let seq;
      if (p.bursts) seq = (typeof p.bursts === 'string') ? parseBurstSequence(p.bursts) : p.bursts;
      else seq = [{ type: 'cpu', len: +p.bt }];
      // Simple mode keeps the old behaviour: a single BT plus one optional I/O
      // value that only enters the WT formula (WT = TAT - (BT + I/O)).
      const simpleIO = (seq.length === 1 && p.io != null && p.io !== '') ? +p.io : 0;
      return {
        pid: String(p.pid),
        at: +p.at,
        priority: (p.priority === '' || p.priority == null) ? null : +p.priority,
        idx: i,
        seq,
        multi: seq.length > 1,
        totalBT: calculateTotalBT(seq),
        totalIO: calculateTotalIO(seq) + simpleIO,
        burstIdx: 0,               // index of the CURRENT cpu burst inside seq
        remaining: seq[0].len,     // remaining units of the current cpu burst
        readyAt: +p.at,            // when the process is (or becomes) ready
        blockedUntil: null,        // set while the process is doing I/O
        firstStart: null, ct: null,
        level: 1, qUsed: 0         // used by RR / MLFQ
      };
    });
  }

  // Add a segment to the timeline, merging contiguous segments of the same pid
  function addSeg(tl, pid, start, end) {
    const last = tl[tl.length - 1];
    if (last && last.pid === pid && last.end === start) { last.end = end; return; }
    tl.push({ pid, start, end });
  }

  /* handleIOBlocking(p, t): the current CPU burst just completed at time t.
     -> 'io'    the process leaves for I/O (blocked until blockedUntil)
     -> 'ready' zero-length I/O, straight back to ready
     -> 'done'  no bursts left, CT = t                                        */
  function handleIOBlocking(p, t, log, note) {
    p.qUsed = 0;
    if (p.burstIdx + 2 < p.seq.length || (p.burstIdx + 1 < p.seq.length)) {
      const io = p.seq[p.burstIdx + 1];
      p.burstIdx += 2; // skip the I/O entry, point at the next CPU burst
      p.remaining = p.seq[p.burstIdx].len;
      if (io.len > 0) {
        p.blockedUntil = t + io.len;
        p.readyAt = t + io.len;
        log.push('Time ' + t + ': ' + p.pid + ' finishes a CPU burst and leaves for I/O (' + io.len + ' units)' + (note || '') + '. It will rejoin the ready queue at time ' + (t + io.len) + '.');
        return 'io';
      }
      p.readyAt = t;
      log.push('Time ' + t + ': ' + p.pid + ' finishes a CPU burst (I/O = 0) and immediately rejoins the ready queue' + (note || '') + '.');
      return 'ready';
    }
    p.ct = t;
    log.push('Time ' + t + ': ' + p.pid + ' finishes its final CPU burst \u2014 CT = ' + t + '.');
    return 'done';
  }

  // Per-process stats + overall summary
  function finish(ps, tl, log) {
    const rows = ps.slice().sort((a, b) => a.idx - b.idx).map(p => {
      const tat = p.ct - p.at;                       // TAT = CT - AT
      const wt = tat - (p.totalBT + p.totalIO);      // WT  = TAT - (Total BT + Total I/O)
      const rt = p.firstStart - p.at;                // RT  = first CPU allocation - AT
      return { ...p, bursts: seqText(p.seq), tat, wt, rt };
    });
    const lastCT = Math.max(...rows.map(r => r.ct));
    // Context switches: CPU changes directly from one process to a DIFFERENT process.
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
        throughput: n / lastCT, switches, overhead,
        efficiency: (1 - overhead) * 100, lastCT
      }
    };
  }

  /* ---------- Generic non-preemptive scheduler (multi-burst aware) ---------- */
  function nonPreemptive(procs, pick, reason) {
    const ps = prep(procs);
    let t = 0, done = 0, guard = 0;
    const tl = [], log = [];
    while (done < ps.length) {
      if (++guard > LIMIT) throw new Error('Simulation exceeded limit \u2014 check your inputs.');
      const ready = ps.filter(p => p.ct === null && p.readyAt <= t);
      if (!ready.length) {
        const next = Math.min(...ps.filter(p => p.ct === null).map(p => p.readyAt));
        addSeg(tl, 'Idle', t, next);
        log.push('Time ' + t + '\u2013' + next + ': CPU is idle (no process is ready \u2014 waiting for arrivals or I/O).');
        t = next; continue;
      }
      const p = pick(ready, t);
      if (p.firstStart === null) p.firstStart = t;
      log.push(reason(t, p, ready));
      const run = p.remaining;
      addSeg(tl, p.pid, t, t + run);
      t += run; p.remaining = 0;
      if (handleIOBlocking(p, t, log, '') === 'done') done++;
    }
    return finish(ps, tl, log);
  }

  /* ---------- FCFS (non-preemptive, criteria: arrival / ready order) ---------- */
  const calculateFCFS = procs => nonPreemptive(
    procs,
    ready => ready.slice().sort((a, b) => a.readyAt - b.readyAt || TIE(a, b))[0],
    (t, p) => 'Time ' + t + ': ' + p.pid + ' is first in FCFS order (ready since time ' + p.readyAt + '), so it runs its CPU burst of ' + p.remaining + ' to completion.'
  );

  /* ---------- SJF (non-preemptive, criteria: next CPU burst length) ---------- */
  const calculateSJF = procs => nonPreemptive(
    procs,
    ready => ready.slice().sort((a, b) => a.remaining - b.remaining || TIE(a, b))[0],
    (t, p, ready) => 'Time ' + t + ': ready = [' + ready.map(r => r.pid + '(BT=' + r.remaining + ')').join(', ') + ']. ' + p.pid + ' has the shortest CPU burst, so SJF runs it to completion.'
  );

  /* ---------- Priority non-preemptive ---------- */
  const calculatePriorityNP = (procs, rule) => nonPreemptive(
    procs,
    ready => ready.slice().sort((a, b) =>
      (rule === 'high' ? b.priority - a.priority : a.priority - b.priority) || TIE(a, b))[0],
    (t, p, ready) => 'Time ' + t + ': ready = [' + ready.map(r => r.pid + '(Pr=' + r.priority + ')').join(', ') + ']. ' + p.pid + ' has the best priority (' + (rule === 'high' ? 'highest' : 'lowest') + ' number wins), so it runs to completion.'
  );

  /* ---------- Generic preemptive unit-time scheduler (multi-burst aware) ---------- */
  function preemptiveUnit(procs, pick, describe) {
    const ps = prep(procs);
    let t = 0, done = 0, running = null, guard = 0;
    const tl = [], log = [];
    while (done < ps.length) {
      if (++guard > LIMIT) throw new Error('Simulation exceeded limit \u2014 check your inputs.');
      const ready = ps.filter(p => p.ct === null && p.readyAt <= t);
      if (!ready.length) { addSeg(tl, 'Idle', t, t + 1); running = null; t++; continue; }
      const p = pick(ready, t);
      if (p.firstStart === null) p.firstStart = t;
      if (running !== p.pid) log.push(describe(t, p, ready, running));
      addSeg(tl, p.pid, t, t + 1);
      p.remaining--; t++;
      if (p.remaining === 0) {
        if (handleIOBlocking(p, t, log, '') === 'done') done++;
        running = null;
      } else running = p.pid;
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

  /* ---------- Round Robin (multi-burst aware) ---------- */
  function calculateRR(procs, qt) {
    qt = +qt;
    const ps = prep(procs);
    const pending = ps.slice().sort(TIE);
    let ai = 0, t = 0, done = 0, running = null, guard = 0;
    const q = [], tl = [], log = [];
    const enqueueEvents = () => {
      // 1) new arrivals, 2) I/O returns \u2014 both join BEFORE a preempted process
      while (ai < pending.length && pending[ai].at <= t) q.push(pending[ai++]);
      for (const p of ps) {
        if (p.ct === null && p.blockedUntil !== null && p.blockedUntil <= t) {
          p.blockedUntil = null;
          q.push(p);
          log.push('Time ' + t + ': ' + p.pid + ' returns from I/O and joins the back of the ready queue.');
        }
      }
    };
    while (done < ps.length) {
      if (++guard > LIMIT) throw new Error('Simulation exceeded limit \u2014 check your inputs.');
      enqueueEvents();
      if (running && running.qUsed === qt) { // quantum expired with CPU work left
        log.push('Time ' + t + ': ' + running.pid + ' used its full quantum (QT = ' + qt + '), remaining = ' + running.remaining + ' \u2014 it goes to the back of the queue.');
        running.qUsed = 0; q.push(running); running = null;
      }
      if (!running) {
        if (!q.length) { addSeg(tl, 'Idle', t, t + 1); t++; continue; }
        running = q.shift();
        if (running.firstStart === null) running.firstStart = t;
        log.push('Time ' + t + ': ' + running.pid + ' is at the front of the ready queue \u2014 it runs (remaining = ' + running.remaining + ').');
      }
      addSeg(tl, running.pid, t, t + 1);
      running.remaining--; running.qUsed++; t++;
      if (running.remaining === 0) {
        const res = handleIOBlocking(running, t, log, ' before using its full quantum');
        if (res === 'done') done++;
        else if (res === 'ready') q.push(running);
        running = null;
      }
    }
    return finish(ps, tl, log);
  }

  /* ---------- MLFQ \u2014 Multi-Level Feedback Queue ----------
     levels: [{qt}, {qt}, ...] where index 0 = Queue 1 = HIGHEST priority.
     Rules implemented:
     - Every process enters Queue 1 (highest) when it arrives.
     - Same queue level -> Round Robin with that queue's quantum.
     - Full quantum used + CPU work remaining -> demoted ONE queue down
       (never below the lowest queue; at the lowest it just goes to the back = RR).
     - Gives up the CPU before the quantum ends (finishes a burst / goes to I/O)
       -> STAYS at the same level. I/O returns re-enter the SAME queue level.
     - A ready process in a higher queue ALWAYS preempts lower queues:
       lower queues never run while a higher queue has a ready process.       */
  function calculateMLFQ(procs, levels) {
    const ps = prep(procs);
    const L = levels.length;
    const qtOf = lvl => +levels[lvl - 1].qt;
    const queues = Array.from({ length: L }, () => []);
    const pending = ps.slice().sort(TIE);
    let ai = 0, t = 0, done = 0, running = null, guard = 0;
    const tl = [], log = [];

    const admitEvents = () => {
      while (ai < pending.length && pending[ai].at <= t) {
        const p = pending[ai++];
        p.level = 1; queues[0].push(p);
        log.push('Time ' + t + ': ' + p.pid + ' arrives and enters Queue 1 (the highest priority queue).');
      }
      for (const p of ps) {
        if (p.ct === null && p.blockedUntil !== null && p.blockedUntil <= t) {
          p.blockedUntil = null;
          queues[p.level - 1].push(p);
          log.push('Time ' + t + ': ' + p.pid + ' returns from I/O and rejoins Queue ' + p.level + ' \u2014 it kept its level because it gave up the CPU before its quantum ended.');
        }
      }
    };
    const highestNonEmpty = () => { for (let i = 0; i < L; i++) if (queues[i].length) return i + 1; return null; };

    while (done < ps.length) {
      if (++guard > LIMIT) throw new Error('Simulation exceeded limit \u2014 check your inputs.');
      admitEvents();

      // 1) Quantum expiry: full QT used and CPU work remains -> demote one level
      if (running && running.qUsed === qtOf(running.level)) {
        const from = running.level;
        running.level = Math.min(L, running.level + 1);
        running.qUsed = 0;
        queues[running.level - 1].push(running);
        log.push('Time ' + t + ': ' + running.pid + ' used the FULL quantum of Queue ' + from + ' (QT = ' + qtOf(from) + ') and still has ' + running.remaining + ' CPU units left \u2014 ' + (running.level === from
          ? 'it is already in the lowest queue, so it goes to the back of Queue ' + from + ' (Round Robin).'
          : 'its priority is decreased: it moves down to Queue ' + running.level + '.'));
        running = null;
      }
      // 2) Preemption: a ready process in a strictly higher queue wins
      if (running) {
        const hi = highestNonEmpty();
        if (hi !== null && hi < running.level) {
          log.push('Time ' + t + ': ' + running.pid + ' (Queue ' + running.level + ') is preempted \u2014 Queue ' + hi + ' has a ready process and higher queues always run first. ' + running.pid + ' stays at Queue ' + running.level + '.');
          running.qUsed = 0;
          queues[running.level - 1].unshift(running); // did not finish its quantum: front of its own queue
          running = null;
        }
      }
      // 3) Dispatch from the highest non-empty queue
      if (!running) {
        const hi = highestNonEmpty();
        if (hi === null) { addSeg(tl, 'Idle', t, t + 1); t++; continue; }
        running = queues[hi - 1].shift();
        if (running.firstStart === null) running.firstStart = t;
        const sameLevel = queues[hi - 1].length;
        const lowerWaiting = queues.slice(hi).reduce((s, qq) => s + qq.length, 0);
        log.push('Time ' + t + ': Queue ' + hi + ' is the highest non-empty queue \u2014 ' + running.pid + ' runs' +
          (sameLevel ? ' (Round Robin with ' + sameLevel + ' other process' + (sameLevel > 1 ? 'es' : '') + ' at this level, QT = ' + qtOf(hi) + ')' : ' (QT = ' + qtOf(hi) + ')') +
          (lowerWaiting ? '; ' + lowerWaiting + ' lower-queue process' + (lowerWaiting > 1 ? 'es' : '') + ' must wait.' : '.'));
      }
      // 4) Run one time unit
      addSeg(tl, running.pid, t, t + 1);
      running.remaining--; running.qUsed++; t++;
      if (running.remaining === 0) {
        const usedFull = running.qUsed === qtOf(running.level);
        const res = handleIOBlocking(running, t, log, usedFull ? '' : ' before its quantum ended, so it STAYS in Queue ' + running.level);
        if (res === 'done') done++;
        else if (res === 'ready') queues[running.level - 1].push(running);
        running = null;
      }
    }
    return finish(ps, tl, log);
  }

  /* ---------- dispatcher ---------- */
  function run(algo, procs, opts = {}) {
    switch (algo) {
      case 'fcfs': return calculateFCFS(procs);
      case 'sjf': return calculateSJF(procs);
      case 'srtf': return calculateSRTF(procs);
      case 'rr': return calculateRR(procs, opts.qt);
      case 'priority-np': return calculatePriorityNP(procs, opts.rule || 'low');
      case 'priority-p': return calculatePriorityP(procs, opts.rule || 'low', +opts.aging || 0);
      case 'mlq': // legacy value, now treated as MLFQ
      case 'mlfq': return calculateMLFQ(procs, (opts.levels && opts.levels.length) ? opts.levels : [{ qt: 2 }, { qt: 4 }, { qt: 8 }]);
      default: throw new Error('Unknown algorithm: ' + algo);
    }
  }

  return {
    run, parseBurstSequence, calculateTotalBT, calculateTotalIO, seqText,
    calculateFCFS, calculateSJF, calculateSRTF, calculateRR,
    calculatePriorityNP, calculatePriorityP, calculateMLFQ,
    calculatePriorityNonPreemptive: calculatePriorityNP,
    calculatePriorityPreemptive: calculatePriorityP
  };
})();

/* ============================ GENERATOR ============================ */
const Generator = (() => {
  const ri = (a, b) => a + Math.floor(Math.random() * (b - a + 1));
  const pickFrom = arr => arr[ri(0, arr.length - 1)];

  const ALGO_LABEL = {
    fcfs: 'FCFS (First Come First Serve, non-preemptive)',
    sjf: 'SJF (Shortest Job First, non-preemptive)',
    srtf: 'SRTF (Shortest Remaining Time First, preemptive)',
    rr: 'Round Robin',
    'priority-np': 'Priority Scheduling (non-preemptive)',
    'priority-p': 'Priority Scheduling (preemptive)',
    mlfq: 'MLFQ (Multi-Level Feedback Queue)'
  };
  const TAG = {
    fcfs: 'FCFS', sjf: 'SJF', srtf: 'SRTF', rr: 'RR',
    'priority-np': 'PRIORITY NP', 'priority-p': 'PRIORITY P', mlfq: 'MLFQ'
  };
  const needsQT = a => a === 'rr' || a === 'mlfq';

  function generateProcesses(s, algo) {
    const n = Math.min(8, Math.max(2, s.n));
    const procs = [];
    for (let i = 0; i < n; i++) {
      procs.push({
        pid: 'P' + (i + 1),
        at: ri(0, Math.max(0, s.atMax)),
        bt: ri(s.btMin, s.btMax),
        priority: ri(1, Math.max(3, Math.min(9, n))),
        io: (!s.multi && s.includeIO) ? ri(1, 3) : 0
      });
    }
    procs.sort((a, b) => a.at - b.at);
    procs.forEach((p, i) => { p.pid = 'P' + (i + 1); });
    // difficulty tweaks (exam-style hidden details)
    if (s.diff === 'hard' || s.diff === 'tricky') procs[1].at = procs[0].at;      // arrival tie
    if (s.diff === 'tricky') {
      procs[1].bt = procs[0].bt;                                                 // equal bursts
      if (algo.indexOf('priority') === 0) procs[1].priority = procs[0].priority; // equal priorities
      procs[procs.length - 1].at = Math.max(procs[procs.length - 1].at, procs[0].bt + procs[1].bt + 2); // idle gap chance
    }
    if (s.multi) {
      // at least half of the processes get CPU/I-O burst sequences
      const count = Math.max(1, Math.ceil(n / 2));
      for (let k = 0; k < count; k++) {
        const p = procs[(k * 2) % n];
        let str = p.bt + ', I' + ri(1, 4) + ', ' + ri(s.btMin, s.btMax);
        if (Math.random() < 0.35) str += ', I' + ri(1, 3) + ', ' + ri(s.btMin, s.btMax);
        p.bursts = str;
      }
    }
    return procs;
  }

  function generateQuestion(s) {
    const pool = ['fcfs', 'sjf', 'srtf', 'rr', 'priority-np', 'priority-p'];
    const algo = s.algo === 'mixed' ? pickFrom(pool) : (s.algo === 'mlq' ? 'mlfq' : s.algo);
    const rule = s.rule === 'random' ? pickFrom(['low', 'high']) : s.rule;
    const qt = needsQT(algo) ? (s.qtMode === 'fixed' ? Math.max(1, +s.qt || 2) : ri(2, 4)) : null;
    let levels = null;
    if (algo === 'mlfq') {
      const L = ri(2, 3);
      levels = [];
      for (let i = 0; i < L; i++) levels.push({ qt: qt * Math.pow(2, i) });
    }
    const procs = generateProcesses(s, algo);
    const usedIO = s.includeIO && !s.multi;

    let st = 'Consider the following ' + procs.length + ' processes. Using ' + ALGO_LABEL[algo] + ' scheduling';
    if (algo === 'rr') st += ' with quantum time QT = ' + qt;
    if (algo.indexOf('priority') === 0) st += ' where the ' + (rule === 'high' ? 'HIGHEST' : 'LOWEST') + ' priority number wins';
    st += ', draw the Gantt chart and compute CT, TAT, WT and RT for every process, then find the average TAT / WT / RT, throughput, number of context switches, overhead and CPU efficiency.';
    if (algo === 'mlfq') {
      st += ' MLFQ rules: every process enters Queue 1 (highest priority) on arrival; ' +
        levels.map((l, i) => 'Queue ' + (i + 1) + ' QT = ' + l.qt).join(', ') +
        '. Processes at the same level run Round Robin. A process that uses its full quantum and still needs CPU is demoted one queue; giving up the CPU before the quantum ends keeps its level; a ready process in a higher queue always preempts lower queues.';
    }
    if (s.multi) st += ' Burst sequences alternate CPU and I/O bursts (example: "5, I3, 4" = CPU 5 \u2192 I/O 3 \u2192 CPU 4). A process is blocked during I/O and rejoins the ready queue when its I/O finishes.';
    if (usedIO) st += ' I/O time is counted in the waiting-time formula: WT = TAT \u2212 (BT + I/O).';

    return {
      algo, algoLabel: ALGO_LABEL[algo], tag: TAG[algo],
      procs, qt: algo === 'rr' ? qt : null, rule, levels,
      statement: st, multi: !!s.multi, usedIO
    };
  }

  return { generateQuestion, generateProcesses, ri };
})();

/* ============================ UI ============================ */
if (typeof document !== 'undefined') (function UI() {
  const $ = id => document.getElementById(id);
  const esc = s => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  const PALETTE = ['#5E9FE8', '#EAC26B', '#72BC8F', '#BF8EDA', '#DE9255', '#DF84A8', '#4FB9C9', '#E97366'];

  /* ---------- view switching ---------- */
  const views = ['home', 'solver', 'practice', 'formulas'];
  function show(view) {
    views.forEach(v => { $('view-' + v).hidden = v !== view; });
    document.querySelectorAll('.nav-btn').forEach(b => b.classList.toggle('active', b.dataset.view === view));
    window.scrollTo(0, 0);
  }
  document.querySelectorAll('.nav-btn').forEach(b => b.addEventListener('click', () => show(b.dataset.view)));
  document.querySelectorAll('.mode-card').forEach(c => c.addEventListener('click', () => show(c.dataset.goto)));

  /* ---------- solver: option visibility (QT only where needed) ---------- */
  const algoSel = $('algo');
  const isPriority = a => a === 'priority-np' || a === 'priority-p';
  // hidden attribute can be overridden by CSS display rules on labels,
  // so toggle display directly as well
  const setVis = (el, show) => { el.hidden = !show; el.style.display = show ? '' : 'none'; };
  function updateQuantumVisibility() {
    const a = algoSel.value;
    setVis($('opt-qt'), a === 'rr');            // QT: only Round Robin
    setVis($('opt-rule'), isPriority(a));
    setVis($('opt-aging'), isPriority(a));
    setVis($('mlfq-config'), a === 'mlfq');     // per-queue QTs: only MLFQ
    document.querySelectorAll('#ptable .col-priority').forEach(el => el.classList.toggle('hide', !isPriority(a)));
    if (a === 'mlfq') buildMlfqRows();
  }
  algoSel.addEventListener('change', updateQuantumVisibility);

  function buildMlfqRows() {
    const n = Math.min(4, Math.max(2, +$('mlfq-levels').value || 3));
    const wrap = $('mlfq-rows');
    const old = [...wrap.querySelectorAll('input')].map(i => i.value);
    const defaults = [2, 4, 8, 16];
    wrap.innerHTML = '';
    for (let i = 0; i < n; i++) {
      const row = document.createElement('div');
      row.className = 'mlq-row';
      row.innerHTML = '<strong>Queue ' + (i + 1) + (i === 0 ? ' \u2014 highest priority' : (i === n - 1 ? ' \u2014 lowest priority' : '')) + '</strong>' +
        '<label>Quantum (QT) <input type="number" min="1" class="mlfq-qt" value="' + (old[i] || defaults[i]) + '"></label>';
      wrap.appendChild(row);
    }
  }
  $('mlfq-levels').addEventListener('input', buildMlfqRows);

  /* ---------- solver: process rows ---------- */
  const pbody = $('pbody');
  const phead = $('phead');
  const burstMode = () => $('burst-mode').value;
  const nBT = () => Math.min(5, Math.max(1, Math.floor(+$('n-bt').value) || 1));
  const nIO = () => Math.min(nBT() - 1, Math.max(0, Math.floor(+$('n-io').value) || 0));

  // Rebuild the table header to match the current burst input mode
  function renderHead() {
    if (burstMode() === 'multi') {
      let h = '<th>PID</th><th>Arrival (AT)</th>';
      for (let i = 1; i <= nBT(); i++) {
        h += '<th>BT' + i + '</th>';
        if (i <= nIO()) h += '<th>IO' + i + '</th>';
      }
      h += '<th class="col-priority">Priority</th><th></th>';
      phead.innerHTML = h;
    } else {
      phead.innerHTML = '<th>PID</th><th>Arrival (AT)</th><th>Burst(s)</th>' +
        '<th class="col-priority">Priority</th><th>I/O Time</th><th></th>';
    }
    phead.querySelector('.col-priority').classList.toggle('hide', !isPriority(algoSel.value));
  }

  function addRow(vals = {}) {
    const tr = document.createElement('tr');
    let html =
      '<td><input class="f-pid" value="' + esc(vals.pid != null ? vals.pid : 'P' + (pbody.children.length + 1)) + '"></td>' +
      '<td><input class="f-at" type="number" min="0" value="' + esc(vals.at != null ? vals.at : 0) + '"></td>';
    if (burstMode() === 'multi') {
      const bts = vals.bts || [];
      const ios = vals.ios || [];
      for (let i = 0; i < nBT(); i++) {
        html += '<td><input class="f-bt-multi" type="number" min="1" placeholder="BT' + (i + 1) + '" value="' + esc(bts[i] != null ? bts[i] : (i === 0 && vals.bt != null ? vals.bt : '')) + '"></td>';
        if (i < nIO()) html += '<td><input class="f-io-multi" type="number" min="0" placeholder="IO' + (i + 1) + '" value="' + esc(ios[i] != null ? ios[i] : '') + '"></td>';
      }
      html += '<td class="col-priority"><input class="f-pr" type="number" value="' + esc(vals.priority != null ? vals.priority : '') + '"></td>' +
        '<td><button class="btn ghost danger btn-remove">Remove</button></td>';
    } else {
      html += '<td><input class="f-bt" placeholder="5   or   5, I3, 4" value="' + esc(vals.bt != null ? vals.bt : '') + '"></td>' +
        '<td class="col-priority"><input class="f-pr" type="number" value="' + esc(vals.priority != null ? vals.priority : '') + '"></td>' +
        '<td><input class="f-io" type="number" min="0" value="' + esc(vals.io != null ? vals.io : 0) + '"></td>' +
        '<td><button class="btn ghost danger btn-remove">Remove</button></td>';
    }
    tr.innerHTML = html;
    tr.querySelector('.btn-remove').addEventListener('click', () => tr.remove());
    tr.querySelector('.col-priority').classList.toggle('hide', !isPriority(algoSel.value));
    pbody.appendChild(tr);
  }

  // Capture current row values so the table can be rebuilt without losing data
  function captureRows() {
    return [...pbody.children].map(tr => {
      const v = {
        pid: tr.querySelector('.f-pid').value,
        at: tr.querySelector('.f-at').value,
        priority: tr.querySelector('.f-pr').value,
      };
      const simple = tr.querySelector('.f-bt');
      if (simple) { // coming FROM simple mode
        v.io = tr.querySelector('.f-io').value;
        const text = simple.value.trim();
        v.bt = text;
        try { // best effort: split a sequence like "5, I3, 4" into columns
          const seq = Engine.parseBurstSequence(text);
          v.bts = seq.filter(b => b.type === 'cpu').map(b => b.len);
          v.ios = seq.filter(b => b.type === 'io').map(b => b.len);
        } catch (e) { v.bts = text === '' ? [] : [text]; v.ios = []; }
      } else { // coming FROM multi mode
        v.bts = [...tr.querySelectorAll('.f-bt-multi')].map(inp => inp.value);
        v.ios = [...tr.querySelectorAll('.f-io-multi')].map(inp => inp.value);
        // build the equivalent text sequence for simple mode
        const parts = [];
        for (let i = 0; i < v.bts.length; i++) {
          if (v.bts[i] === '') break;
          parts.push(v.bts[i]);
          if (i < v.ios.length && v.bts[i + 1] != null && v.bts[i + 1] !== '') parts.push('I' + (v.ios[i] === '' ? 0 : v.ios[i]));
        }
        v.bt = parts.join(', ');
        v.io = 0;
      }
      return v;
    });
  }

  function rebuildTable() {
    // a valid sequence ends with a CPU burst, so at most BT-1 I/O slots
    if ($('n-bt').value === '' || +$('n-bt').value < 1) $('n-bt').value = 1;
    if (+$('n-io').value > nBT() - 1) $('n-io').value = nBT() - 1;
    if ($('n-io').value === '' || +$('n-io').value < 0) $('n-io').value = 0;
    const rows = captureRows();
    renderHead();
    pbody.innerHTML = '';
    if (rows.length) rows.forEach(v => addRow(v));
    else { addRow(); addRow(); addRow(); }
  }

  function updateBurstModeVisibility() {
    const multi = burstMode() === 'multi';
    setVis($('opt-nbt'), multi);
    setVis($('opt-nio'), multi);
    rebuildTable();
  }
  $('burst-mode').addEventListener('change', updateBurstModeVisibility);
  $('n-bt').addEventListener('change', rebuildTable);
  $('n-io').addEventListener('change', rebuildTable);

  function collectProcesses() {
    const rows = [...pbody.children];
    if (!rows.length) throw new Error('Add at least one process.');
    const seen = new Set(), procs = [];
    const needPr = isPriority(algoSel.value);
    const multi = burstMode() === 'multi';
    rows.forEach((tr, i) => {
      const pid = tr.querySelector('.f-pid').value.trim();
      const at = tr.querySelector('.f-at').value.trim();
      const pr = tr.querySelector('.f-pr').value.trim();
      if (!pid) throw new Error('Row ' + (i + 1) + ': PID is required.');
      if (seen.has(pid)) throw new Error('Duplicate PID "' + pid + '" \u2014 every process needs a unique name.');
      seen.add(pid);
      if (at === '' || isNaN(+at) || +at < 0) throw new Error(pid + ': Arrival Time must be a number \u2265 0.');
      if (needPr && (pr === '' || isNaN(+pr))) throw new Error(pid + ': Priority is required for priority scheduling.');
      let seq, io = 0;
      if (multi) {
        const bts = [...tr.querySelectorAll('.f-bt-multi')].map(inp => inp.value.trim());
        const ios = [...tr.querySelectorAll('.f-io-multi')].map(inp => inp.value.trim());
        seq = [];
        for (let k = 0; k < bts.length; k++) {
          if (bts[k] === '') {
            if (k === 0) throw new Error(pid + ': BT1 is required.');
            // this process simply has fewer bursts \u2014 but check nothing was typed after the gap
            for (let m = k + 1; m < bts.length; m++) if (bts[m] !== '') throw new Error(pid + ': BT' + (m + 1) + ' has a value but BT' + (k + 1) + ' is empty \u2014 fill bursts from left to right.');
            if (ios[k - 1] != null && ios[k - 1] !== '' && +ios[k - 1] > 0) throw new Error(pid + ': IO' + k + ' has a value but no CPU burst follows it \u2014 a process must end with a CPU burst.');
            break;
          }
          const b = +bts[k];
          if (isNaN(b) || b <= 0) throw new Error(pid + ': BT' + (k + 1) + ' must be a number > 0.');
          seq.push({ type: 'cpu', len: b });
          if (k < ios.length && bts[k + 1] != null && bts[k + 1] !== '') {
            const v = ios[k] === '' ? 0 : +ios[k];
            if (isNaN(v) || v < 0) throw new Error(pid + ': IO' + (k + 1) + ' must be a number \u2265 0.');
            seq.push({ type: 'io', len: v });
          }
        }
      } else {
        const btText = tr.querySelector('.f-bt').value.trim();
        const ioText = tr.querySelector('.f-io').value.trim();
        if (!btText) throw new Error(pid + ': Burst is required \u2014 a number like "5" or a sequence like "5, I3, 4".');
        try { seq = Engine.parseBurstSequence(btText); }
        catch (e) { throw new Error(pid + ': ' + e.message); }
        if (ioText !== '' && (isNaN(+ioText) || +ioText < 0)) throw new Error(pid + ': I/O Time must be a number \u2265 0.');
        io = ioText === '' ? 0 : +ioText;
      }
      procs.push({ pid, at: +at, bursts: seq, io, priority: pr === '' ? null : +pr });
    });
    return procs;
  }

  function collectOpts() {
    const a = algoSel.value;
    const opts = {};
    if (a === 'rr') {
      opts.qt = +$('qt').value;
      if (!(opts.qt > 0)) throw new Error('Quantum Time (QT) must be a number > 0 for Round Robin.');
    }
    if (isPriority(a)) { opts.rule = $('rule').value; opts.aging = +$('aging').value || 0; }
    if (a === 'mlfq') {
      if (!document.querySelector('#mlfq-rows .mlfq-qt')) buildMlfqRows();
      opts.levels = [...document.querySelectorAll('#mlfq-rows .mlfq-qt')].map(inp => ({ qt: +inp.value }));
      if (opts.levels.some(l => !(l.qt > 0))) throw new Error('Every MLFQ queue needs a quantum > 0.');
    }
    return opts;
  }

  function labelOf(a, opts) {
    switch (a) {
      case 'fcfs': return 'FCFS';
      case 'sjf': return 'SJF';
      case 'srtf': return 'SRTF';
      case 'rr': return 'Round Robin (QT = ' + opts.qt + ')';
      case 'priority-np': return 'Priority \u2014 Non-Preemptive (' + (opts.rule === 'high' ? 'highest' : 'lowest') + ' number wins)';
      case 'priority-p': return 'Priority \u2014 Preemptive (' + (opts.rule === 'high' ? 'highest' : 'lowest') + ' number wins)';
      case 'mlfq': return 'MLFQ (' + opts.levels.map((l, i) => 'Q' + (i + 1) + ' QT=' + l.qt).join(', ') + ')';
      default: return a;
    }
  }

  /* ---------- shared solution renderer ---------- */
  const SEC = 'margin:20px 0 8px;font-size:12.5px;font-weight:700;letter-spacing:.09em;text-transform:uppercase;color:var(--text2)';
  function renderResults(container, res, meta) {
    const colors = {}; let ci = 0;
    res.timeline.forEach(s => { if (s.pid !== 'Idle' && !(s.pid in colors)) colors[s.pid] = PALETTE[ci++ % PALETTE.length]; });
    const lastEnd = res.timeline[res.timeline.length - 1].end;

    const gantt = '<div class="gantt"><div class="gantt-track">' + res.timeline.map((s, i) =>
      '<div class="g-block' + (s.pid === 'Idle' ? ' idle' : '') + '" style="width:' + (((s.end - s.start) / lastEnd) * 100) + '%;' +
      (s.pid === 'Idle' ? '' : 'background:' + colors[s.pid]) + '">' + esc(s.pid) +
      '<i class="g-t">' + s.start + '</i>' +
      (i === res.timeline.length - 1 ? '<i class="g-tend">' + s.end + '</i>' : '') +
      '</div>').join('') + '</div></div>';

    const anyMulti = res.rows.some(r => r.multi);
    const showPr = !!meta.showPriority;
    let head = '<tr><th>PID</th><th>AT</th>' + (anyMulti ? '<th>Bursts (CPU / I-O)</th>' : '') + '<th>' + (anyMulti ? 'Total BT' : 'BT') + '</th>' +
      (showPr ? '<th>Priority</th>' : '') + '<th>' + (anyMulti ? 'Total I/O' : 'I/O') + '</th><th>First Start</th><th>CT</th><th>TAT</th><th>WT</th><th>RT</th></tr>';
    const body = res.rows.map(r =>
      '<tr><td><strong>' + esc(r.pid) + '</strong></td><td>' + r.at + '</td>' +
      (anyMulti ? '<td>' + esc(r.bursts) + '</td>' : '') +
      '<td>' + r.totalBT + '</td>' +
      (showPr ? '<td>' + (r.priority == null ? '\u2014' : r.priority) + '</td>' : '') +
      '<td>' + r.totalIO + '</td><td>' + r.firstStart + '</td><td>' + r.ct + '</td><td>' + r.tat + '</td><td>' + r.wt + '</td><td>' + r.rt + '</td></tr>').join('');

    const f = x => (Math.round(x * 1000) / 1000);
    const cards = [
      [f(res.summary.avgTAT), 'Avg TAT'], [f(res.summary.avgWT), 'Avg WT'], [f(res.summary.avgRT), 'Avg RT'],
      [f(res.summary.throughput) + ' /unit', 'Throughput'], [res.summary.switches, 'Context switches'],
      [f(res.summary.overhead), 'Overhead'], [f(res.summary.efficiency) + '%', 'Efficiency'], [res.summary.lastCT, 'Last CT']
    ].map(c => '<div class="sum-card"><b>' + c[0] + '</b><span>' + c[1] + '</span></div>').join('');

    const steps = '<ol class="steps">' + res.log.map(l => '<li>' + esc(l) + '</li>').join('') + '</ol>';

    container.innerHTML =
      '<div class="card">' +
      '<div class="q-head"><h3>Solution \u2014 ' + esc(meta.label) + '</h3>' +
      '<div class="btn-row" style="margin:0"><button class="btn ghost btn-print">Print / Export</button></div></div>' +
      '<h4 style="' + SEC + '">Gantt chart</h4>' + gantt +
      '<h4 style="' + SEC + '">Results table</h4><div class="table-wrap"><table>' + head + body + '</table></div>' +
      '<h4 style="' + SEC + '">Summary</h4><div class="summary-grid">' + cards + '</div>' +
      '<h4 style="' + SEC + '">Step-by-step explanation</h4>' + steps +
      '</div>';
    container.querySelector('.btn-print').addEventListener('click', () => window.print());
  }

  /* ---------- solver actions ---------- */
  $('btn-add').addEventListener('click', () => addRow());
  $('btn-reset').addEventListener('click', () => {
    pbody.innerHTML = ''; addRow(); addRow(); addRow();
    $('solver-results').innerHTML = ''; $('solver-error').hidden = true;
  });
  $('btn-sample').addEventListener('click', loadSample);
  function loadSample() {
    pbody.innerHTML = '';
    addRow({ pid: 'P1', at: 0, bt: '5', priority: 2, io: 0 });
    addRow({ pid: 'P2', at: 1, bt: '3', priority: 1, io: 0 });
    addRow({ pid: 'P3', at: 2, bt: '8', priority: 3, io: 0 });
    addRow({ pid: 'P4', at: 3, bt: '6', priority: 2, io: 0 });
    $('qt').value = 2;
  }
  $('btn-calc').addEventListener('click', () => {
    const err = $('solver-error');
    err.hidden = true;
    try {
      const procs = collectProcesses();
      const opts = collectOpts();
      const res = Engine.run(algoSel.value, procs, opts);
      renderResults($('solver-results'), res, { label: labelOf(algoSel.value, opts), showPriority: isPriority(algoSel.value) });
    } catch (e) {
      err.textContent = e.message; err.hidden = false;
      $('solver-results').innerHTML = '';
    }
  });

  /* ---------- practice generator ---------- */
  const gAlgo = $('g-algo');
  function updatePracticeQtVisibility() {
    const a = gAlgo.value;
    const showQT = a === 'rr' || a === 'mlfq' || a === 'mixed'; // QT only when it can be needed
    setVis($('g-qtmode-wrap'), showQT);
    setVis($('g-qt-wrap'), showQT && $('g-qtmode').value === 'fixed');
  }
  gAlgo.addEventListener('change', updatePracticeQtVisibility);
  $('g-qtmode').addEventListener('change', updatePracticeQtVisibility);

  let currentQ = null, revealed = false;
  function renderQuestionTable(q) {
    const isPr = q.algo.indexOf('priority') === 0;
    let html = '<tr><th>PID</th><th>AT</th><th>' + (q.multi ? 'Bursts (CPU / I-O)' : 'BT') + '</th>' +
      (isPr ? '<th>Priority</th>' : '') + (q.usedIO ? '<th>I/O</th>' : '') + '</tr>';
    html += q.procs.map(p =>
      '<tr><td><strong>' + esc(p.pid) + '</strong></td><td>' + p.at + '</td><td>' + esc(p.bursts ? p.bursts : p.bt) + '</td>' +
      (isPr ? '<td>' + p.priority + '</td>' : '') + (q.usedIO ? '<td>' + p.io + '</td>' : '') + '</tr>').join('');
    $('q-table').innerHTML = html;
  }
  function generate() {
    const settings = {
      algo: gAlgo.value, n: +$('g-n').value || 4, atMax: +$('g-atmax').value || 8,
      btMin: Math.max(1, +$('g-btmin').value || 1), btMax: Math.max(1, +$('g-btmax').value || 9),
      includeIO: $('g-io').value === 'yes', multi: $('g-multi').value === 'yes',
      rule: $('g-rule').value, qtMode: $('g-qtmode').value, qt: +$('g-qt').value || 2,
      diff: $('g-diff').value
    };
    if (settings.btMax < settings.btMin) settings.btMax = settings.btMin;
    currentQ = Generator.generateQuestion(settings);
    revealed = false;
    $('q-algo-pill').textContent = currentQ.tag;
    $('q-statement').textContent = currentQ.statement;
    renderQuestionTable(currentQ);
    $('question-card').hidden = false;
    $('btn-reveal').textContent = 'Reveal solution';
    $('practice-results').innerHTML = '';
  }
  $('btn-generate').addEventListener('click', generate);
  $('btn-newq').addEventListener('click', generate);
  $('btn-reveal').addEventListener('click', () => {
    if (!currentQ) return;
    revealed = !revealed;
    if (revealed) {
      const res = Engine.run(currentQ.algo, currentQ.procs, { qt: currentQ.qt, rule: currentQ.rule, levels: currentQ.levels });
      const label = currentQ.algo === 'mlfq'
        ? 'MLFQ (' + currentQ.levels.map((l, i) => 'Q' + (i + 1) + ' QT=' + l.qt).join(', ') + ')'
        : currentQ.algoLabel + (currentQ.qt ? ' (QT = ' + currentQ.qt + ')' : '');
      renderResults($('practice-results'), res, { label, showPriority: currentQ.algo.indexOf('priority') === 0 });
      $('btn-reveal').textContent = 'Hide solution';
    } else {
      $('practice-results').innerHTML = '';
      $('btn-reveal').textContent = 'Reveal solution';
    }
  });

  /* ---------- boot ---------- */
  updateBurstModeVisibility(); // renders the table header + starter rows
  updateQuantumVisibility();
  updatePracticeQtVisibility();
  buildMlfqRows();

  // QA / demo deep links
  if (location.hash === '#demo') { show('solver'); loadSample(); $('btn-calc').click(); }
  else if (location.hash === '#demo-mlfq') {
    show('solver'); algoSel.value = 'mlfq'; updateQuantumVisibility();
    pbody.innerHTML = '';
    addRow({ pid: 'P1', at: 0, bt: '10', io: 0 });
    addRow({ pid: 'P2', at: 0, bt: '4', io: 0 });
    addRow({ pid: 'P3', at: 1, bt: '2, I5, 3', io: 0 });
    $('btn-calc').click();
  }
  else if (location.hash === '#demo-multi') {
    show('solver');
    $('burst-mode').value = 'multi'; $('n-bt').value = 3; $('n-io').value = 2;
    updateBurstModeVisibility();
    pbody.innerHTML = '';
    addRow({ pid: 'P1', at: 0, bts: [5, 4, 6], ios: [3, 2] });
    addRow({ pid: 'P2', at: 1, bts: [3, 2], ios: [4] });
    addRow({ pid: 'P3', at: 2, bts: [8], ios: [] });
    $('btn-calc').click();
  }
  else if (location.hash === '#demo-practice') { show('practice'); $('btn-generate').click(); $('btn-reveal').click(); }
})();

/* ---------- node exports for testing ---------- */
if (typeof module !== 'undefined') module.exports = { Engine, Generator };
