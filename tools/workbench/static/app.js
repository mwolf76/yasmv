'use strict';
const $ = id => document.getElementById(id);
const state = {revision: null, dirty: true, examples: [], jobs: [], job: null, artifact: null, comparison: null, step: 0, importing: false, scenario: null};
const node = (tag, text, className) => { const e = document.createElement(tag); if (text !== undefined) e.textContent = text; if (className) e.className = className; return e; };
const option = (label, value) => { const e = node('option', label); e.value = value; return e; };
async function api(path, body) {
  const response = await fetch('/api/' + path, body === undefined ? {} : {method: 'POST', headers: {'Content-Type': 'application/json'}, body: JSON.stringify(body)});
  const result = await response.json();
  if (!response.ok) throw new Error(result.error || 'Request failed');
  return result;
}
function notice(error) { $('notice').hidden = !error; $('notice').textContent = error ? String(error.message || error) : ''; }
function action(id, fn) { $(id).addEventListener('click', async () => { notice(null); try { await fn(); } catch (e) { notice(e); } }); }
function remember() {
  localStorage.setItem('yasmv-session', JSON.stringify({revision: state.revision?.id, trace: state.artifact?.id, comparison: state.comparison?.id, job: state.job, step: state.step, scenario: state.scenario?.id}));
}
function markDirty() { state.dirty = true; $('dirty').textContent = 'Unsaved changes'; }
for (const id of ['source', 'model-name', 'root', 'inputs', 'goals', 'watches', 'properties', 'scenario-metadata']) $(id).addEventListener('input', markDirty);
function fillEditor(revision) {
  $('model-name').value = revision.name;
  $('source').value = revision.source;
  $('root').value = revision.root || '';
  $('scenario-metadata').value = JSON.stringify(revision.scenario || null, null, 2);
  for (const name of ['inputs', 'goals', 'watches', 'properties']) $(name).value = JSON.stringify(revision[name] || {}, null, 2);
  $('property').replaceChildren(option('Select a safety property…', ''));
  for (const name of Object.keys(revision.properties || {})) $('property').append(option(name, name));
  if ($('property').options.length > 1) $('property').selectedIndex = 1;
  $('goal').replaceChildren(option('Custom expression', ''));
  for (const [name, expression] of Object.entries(revision.goals || {})) $('goal').append(option(name, expression));
  if ($('goal').options.length > 1) { $('goal').selectedIndex = 1; $('target').value = $('goal').value; }
  else $('target').value = '';
}
async function refreshRevisions() {
  const revisions = await api('revisions');
  $('revision').replaceChildren(option('Choose a revision…', ''));
  for (const rev of revisions) $('revision').append(option(`${rev.name} · ${rev.id.slice(0, 8)}`, rev.id));
  $('revision').value = state.revision?.id || '';
}
async function selectRevision(id) {
  state.revision = await api('revisions/' + id);
  state.dirty = false;
  fillEditor(state.revision);
  $('revision').value = id;
  $('dirty').textContent = 'Saved · ' + id.slice(0, 8);
  $('revision-id').textContent = id;
  state.artifact = null; state.comparison = null; state.step = 0; state.job = null;
  $('result-title').textContent = 'Revision selected';
  $('result-detail').textContent = 'Validate or query this saved revision, or select a previous job.';
  $('result-panel').className = 'panel result-panel';
  for (const id of ['cancel', 'progress', 'diagnostics', 'explanation', 'replay-difference', 'proof-detail']) $(id).hidden = true;
  renderTrace(); await refreshTraces(); state.scenario = null; await refreshScenarios(); remember();
}
$('revision').addEventListener('change', async () => { try { if ($('revision').value) await selectRevision($('revision').value); } catch (e) { notice(e); } });
$('example').addEventListener('change', () => {
  if ($('example').value === '') return;
  const model = state.examples[Number($('example').value)];
  fillEditor(model); $('depth').value = model.default_depth; markDirty(); $('editor').open = true;
});
$('goal').addEventListener('change', () => { if ($('goal').value) $('target').value = $('goal').value; });
$('target').addEventListener('input', () => { if ($('goal').value !== $('target').value) $('goal').value = ''; });
function ready() {
  if (!state.revision || state.dirty) throw new Error('Save the current source and configuration as a revision before running a query.');
}
function number(id, min, max) { const value = Number($(id).value); if (!Number.isInteger(value) || value < min || value > max) throw new Error(`${id} must be an integer from ${min} to ${max}.`); return value; }
async function submit(query) {
  ready();
  const timeout = number('timeout', 1, 300);
  const request = {version: 1, request_id: crypto.randomUUID(), revision: state.revision.id, hard_timeout: timeout,
    query: query.operation.endsWith('-scenario') ? query : {...query, limits: {...query.limits, wall_ms: timeout * 1000}}};
  const {id} = await api('jobs', request);
  state.job = id; remember();
  await refreshJobs();
  return id;
}
action('save', async () => {
  const revision = {name: $('model-name').value, source: $('source').value, root: $('root').value};
  for (const name of ['inputs', 'goals', 'watches', 'properties']) revision[name] = JSON.parse($(name).value);
  const mapping = JSON.parse($('scenario-metadata').value);
  if (mapping !== null) revision.scenario = mapping;
  const saved = await api('revisions', revision);
  await refreshRevisions(); await selectRevision(saved.id);
  await submit({operation: 'validate-model'});
});
action('search', async () => {
  const target = $('target').value.trim();
  if (!target) throw new Error('Enter a target expression.');
  await submit({operation: 'reach', target, limits: {depth: number('depth', 0, 10000)}, assumptions: $('assumptions').value.split('\n').map(s => s.trim()).filter(Boolean)});
});
action('shortest', async () => {
  const target = $('target').value.trim();
  if (!target) throw new Error('Enter a target expression.');
  await submit({operation: 'shortest-reach', target, limits: {depth: number('depth', 0, 10000)}, assumptions: $('assumptions').value.split('\n').map(s => s.trim()).filter(Boolean)});
});
for (const operation of ['check-property', 'prove-property']) action(operation, () => {
  if (!$('property').value) throw new Error('Save and select a named safety property.');
  return submit({operation, strategy: operation === 'prove-property' ? $('proof-strategy').value : 'auto', property: $('property').value, limits: {depth: number('depth', operation === 'prove-property' ? 1 : 0, 10000)}, assumptions: $('assumptions').value.split('\n').map(s => s.trim()).filter(Boolean)});
});
action('pick', () => submit({operation: 'pick-state', assumptions: $('assumptions').value.split('\n').map(s => s.trim()).filter(Boolean)}));
action('cancel', () => api('jobs/' + state.job + '/cancel', {}));
function describeResult(result, query) {
  if (result.status === 'error') return ['Query failed', 'Read the diagnostics below. The saved revision is unchanged.', 'error'];
  if (result.status === 'unknown') return ['Inconclusive · ' + result.stop_reason.replaceAll('_', ' '), 'No reachability or safety conclusion follows from this interrupted or incomplete computation.', 'unknown'];
  if (result.outcome === 'proven') return ['Safety property proved', result.proof_method === 'interpolation' ? 'A verified inductive invariant establishes the property under the recorded assumptions.' : 'Verified k-induction establishes the selected property for all reachable states under the recorded assumptions.', 'success'];
  if (result.outcome === 'violated') return ['Safety property violated at depth ' + (result.trace.steps.length - 1), 'A shortest reachable counterexample passed model replay.', 'error'];
  if (result.outcome === 'holds_bounded') return ['Property holds through depth ' + query.limits.depth, result.proof?.step_status === 'satisfiable' ? 'Induction was inconclusive. Its step assignment may be unreachable; unbounded safety is unknown.' : 'No counterexample within this bound. Unbounded safety is unknown.', 'unknown'];
  if (query.operation === 'shortest-reach' && result.outcome === 'reachable') return ['Shortest witness at depth ' + result.optimality.depth, 'Every smaller depth was UNSAT. This witness passed model replay; the certificate measures transitions.', 'success'];
  if (query.operation.startsWith('explain-')) {
    if (result.outcome === 'satisfiable') return ['Query is feasible', 'No impossibility explanation applies. Run a search to obtain a concrete trace.', 'success'];
    return [query.operation === 'explain-step' ? 'No valid next transition' : query.operation === 'explain-init' ? 'Initial constraints are inconsistent' : 'Goal impossible through depth ' + query.limits.depth,
      'Each reported subset reproduces UNSAT under the fixed background below. This is not an unbounded safety proof.', 'unknown'];
  }
  if (query.operation === 'export-scenario') return ['Executable scenario exported', 'The source trace passed model replay. Download the scenario or replay it against either receiver.', 'success'];
  if (query.operation === 'replay-scenario') {
    const replay = result.implementation_replay;
    return result.outcome === 'matched' ? ['Implementation matched the scenario', replay.duplicate_execution ? 'Duplicate execution reproduced in the faulty receiver.' : 'All observations matched the exported expectations.', 'success'] :
      ['Implementation diverged at step ' + replay.first_divergence.step, replay.duplicate_execution ? 'The first differing observation is shown below.' : 'Duplicate execution has not been reproduced. The first differing observation is shown below.', 'unknown'];
  }
  if (result.outcome === 'unreachable' && result.scope === 'unbounded') return ['Goal proved unreachable', 'A verified inductive invariant excludes the target under the recorded assumptions.', 'success'];
  if (result.outcome === 'unreachable') return [`No witness through depth ${query.limits.depth}`, 'Bounded negative result. Reachability beyond this bound is unknown; this is not a safety proof.', 'unknown'];
  if (result.outcome === 'reachable') return [`Goal reached at depth ${result.trace.steps.length - 1}`, 'A concrete witness was found and independently replayed in a fresh checker process.', 'success'];
  if (result.outcome === 'deadlocked') return ['Continuation blocked', 'No extension meets the constraint at the pinned source state. If the constraint conflicts with the prefix, start a fresh search. The child preserves the valid prefix.', 'unknown'];
  if (result.outcome === 'simulated') return ['Child trace created', 'The selected prefix is unchanged. The child and its parent have passed replay validation.', 'success'];
  if (query.operation === 'validate-model') return ['Model validated', 'Parsing, types, and model structure are valid. Use Pick initial state to check that an initial state exists.', 'success'];
  if (query.operation === 'validate-trace') return result.outcome === 'valid' ? ['Trace passed replay', 'Identity, values, transitions, generating constraints, and parent prefix were checked.', 'success'] : ['Trace failed replay', 'This import remains untrusted and cannot be used as evidence.', 'error'];
  return result.outcome === 'satisfiable' ? ['Initial state found', 'This initial state has passed replay validation.', 'success'] : ['No initial state', 'The model and current assumptions admit no initial state.', 'unknown'];
}
function renderAnalysisEvidence(result) {
  const container = $('proof-detail'); container.replaceChildren();
  container.hidden = !result.proof && !result.optimality;
  if (container.hidden) return;
  const depths = values => !values?.length ? 'none required' : values.length > 12 ? `${values[0]} through ${values.at(-1)}` : values.join(', ');
  if (result.optimality) container.append(node('p', `Shortest witness: ${result.optimality.depth} transitions. UNSAT at smaller depths: ${depths(result.optimality.unsat_depths)}.`));
  const proof = result.proof;
  if (proof) {
    if (proof.property) container.append(node('p', `Property: ${proof.property.name} · ${proof.property.expression}`));
    if (proof.assumptions?.length) container.append(node('p', 'Under assumptions: ' + proof.assumptions.join('; ')));
    if (proof.base_unsat_depths?.length) container.append(node('p', 'No reachable violation at depths: ' + depths(proof.base_unsat_depths) + '.'));
    if (proof.step_status) container.append(node('p', `Induction step at k = ${proof.induction_depth}: ${proof.step_status === 'unsatisfiable' ? 'UNSAT' : 'SAT; the assignment may be unreachable'}.`));
    if (proof.verified) container.append(node('p', result.proof_method === 'interpolation' ? 'Initial-state containment, transition closure, and target exclusion were checked in fresh solvers.' : 'All base obligations and the induction step were rechecked in fresh solvers.'));
    if (proof.vacuous) container.append(node('p', 'No initial states satisfy the model and recorded assumptions.'));
    const interpolation = result.statistics?.interpolation;
    if (interpolation) container.append(node('p', `Interpolation: ${interpolation.images} image queries, ${interpolation.restarts} restarts, suffix horizon ${interpolation.horizon}.`));
  }
  const details = node('details');
  details.append(node('summary', proof?.induction_counterexample ? 'Inspect induction assignment and analysis evidence' : 'Inspect analysis evidence'));
  details.append(node('pre', JSON.stringify({optimality: result.optimality, proof}, null, 2)));
  container.append(details);
}
let lastPublished = null;
async function refreshJobs() {
  state.jobs = await api('jobs');
  $('job-count').textContent = state.jobs.length;
  $('jobs').replaceChildren();
  for (const job of [...state.jobs].reverse()) {
    const button = node('button', undefined, 'job' + (job.request.request_id === state.job ? ' selected' : ''));
    button.append(node('strong', job.request.query.operation + ' · ' + job.request.revision.slice(0, 6)), node('small', job.result ? job.result.status + ' / ' + (job.result.outcome || job.result.stop_reason) : 'Running…'));
    button.addEventListener('click', async () => { state.job = job.request.request_id; lastPublished = null; remember(); try { await refreshJobs(); } catch (e) { notice(e); } });
    $('jobs').append(button);
  }
  const job = state.jobs.find(j => j.request.request_id === state.job);
  if (!job) return;
  $('cancel').hidden = !job.running;
  $('progress').hidden = !job.running;
  $('diagnostics').hidden = true;
  $('explanation').hidden = true;
  $('replay-difference').hidden = true;
  $('proof-detail').hidden = true;
  if (job.running) {
    $('result-panel').className = 'panel result-panel';
    $('result-title').textContent = 'Working · ' + job.request.query.operation;
    const response = await fetch(`/api/jobs/${state.job}/events`);
    const events = (await response.text()).trim().split('\n').filter(Boolean).map(line => JSON.parse(line));
    const progress = events.filter(e => e.event === 'progress').at(-1);
    $('result-detail').textContent = progress ? `${({'analysis': 'Checker running', 'replay': 'Validating model trace', 'implementation-replay': 'Replaying implementation'}[progress.phase] || progress.phase)} · ${(progress.elapsed_ms / 1000).toFixed(1)} s in this phase · isolated worker` : 'Starting an isolated worker…';
  } else {
    const [title, detail, style] = describeResult(job.result, job.request.query);
    $('result-title').textContent = title;
    $('result-detail').textContent = detail + ' · Revision ' + job.request.revision.slice(0, 8);
    $('result-panel').className = 'panel result-panel ' + style;
    renderExplanation(job);
    renderAnalysisEvidence(job.result);
    if (job.result.implementation_replay?.first_divergence) {
      $('replay-difference').hidden = false;
      $('replay-difference').textContent = JSON.stringify(job.result.implementation_replay.first_divergence, null, 2);
    }
    const diagnostics = job.result.diagnostics || [];
    if (diagnostics.length) { $('diagnostics').hidden = false; $('diagnostics').textContent = diagnostics.map(d => `${d.code}: ${d.message}${d.primary?.line ? ' (line ' + d.primary.line + ')' : ''}`).join('\n'); }
    if (lastPublished !== state.job) {
      lastPublished = state.job;
      if (state.revision?.id === job.request.revision && job.result.trace_id) {
        await refreshTraces(); await selectTrace(job.result.trace_id);
      }
      if (state.revision?.id === job.request.revision && job.result.scenario_id) {
        await selectScenario(job.result.scenario_id); await refreshScenarios();
      }
      state.importing = false;
    }
  }
}
async function refreshTraces() {
  const values = await api('traces');
  for (const id of ['trace', 'compare']) {
    const selected = id === 'trace' ? state.artifact?.id : state.comparison?.id;
    $(id).replaceChildren(option(id === 'trace' ? 'Choose a trace…' : 'No comparison', ''));
    for (const trace of values) {
      if (id === 'trace' && trace.revision !== state.revision?.id) continue;
      $(id).append(option(`${trace.operation} · ${trace.steps} states · ${trace.id.slice(0, 8)} · rev ${trace.revision.slice(0, 6)}`, trace.id));
    }
    $(id).value = selected || '';
  }
}
async function selectTrace(id) {
  state.artifact = id ? await api('traces/' + id) : null;
  state.step = 0; $('trace').value = id || ''; renderTrace(); remember();
}
$('trace').addEventListener('change', async () => { try { await selectTrace($('trace').value); } catch (e) { notice(e); } });
$('compare').addEventListener('change', async () => { try { state.comparison = $('compare').value ? await api('traces/' + $('compare').value) : null; renderTrace(); remember(); } catch (e) { notice(e); } });
function table(artifact, step, reference, comparing = false) {
  const frame = artifact.trace?.steps?.[step];
  if (!frame) return node('p', 'This trace has no state at the selected step.', 'muted');
  const rows = Object.entries(frame.values);
  const watches = Object.entries(artifact.watches || {});
  const t = node('table'); const head = node('tr'); head.append(node('th', 'SYMBOL / WATCH'), node('th', comparing ? 'COMPARISON VALUE' : 'VALUE')); t.append(head);
  for (const [name, value, watch] of [...rows.map(r => [...r, false]), ...watches.map(([name, values]) => [name, values[step], true])]) {
    const ref = watch ? reference?.watches?.[name]?.[comparing ? step : step - 1] : reference?.trace?.steps?.[comparing ? step : step - 1]?.values?.[name];
    const changed = ref !== undefined && JSON.stringify(ref) !== JSON.stringify(value);
    const row = node('tr', undefined, (watch ? 'watch ' : '') + (changed ? comparing ? 'different' : 'changed' : ''));
    row.append(node('td', (watch ? '◈ ' : '') + name), node('td', value === null || value === undefined ? 'unassigned' : typeof value === 'object' ? JSON.stringify(value) : String(value)));
    t.append(row);
  }
  return t;
}
function renderTrace() {
  const artifact = state.artifact; const trace = artifact?.trace;
  const trusted = Boolean(artifact?.validated);
  $('trust').textContent = trace ? trusted ? 'Replay validated' : 'Untrusted import' : 'No trace';
  $('trust').className = 'badge ' + (trace ? trusted ? 'valid' : 'untrusted' : '');
  $('export').disabled = !trusted;
  $('branch').disabled = !trusted || artifact.revision !== state.revision?.id;
  $('explain-step').disabled = $('branch').disabled;
  $('export-scenario').disabled = $('branch').disabled || !state.revision?.scenario;
  $('timeline').replaceChildren();
  if (!trace) {
    $('trace-description').textContent = 'Replay-validated traces will appear here. Select a step to inspect or branch.';
    $('inspector').textContent = 'No state selected.'; $('comparison').textContent = 'Choose another trace to compare the same step.'; return;
  }
  $('trace-description').textContent = `${trace.steps.length} states · ${trace.steps.length - 1} transitions${trace.branch ? ' · Branch prefix: ' + trace.branch.prefix_length + ' states' : ''}. Actions label outgoing transitions; the final action has not executed. Amber values changed since the previous step; red values differ from the selected trace.`;
  for (const [index, frame] of trace.steps.entries()) {
    const button = node('button', undefined, 'step' + (index === state.step ? ' selected' : ''));
    button.setAttribute('aria-pressed', String(index === state.step));
    button.append(node('small', 'STEP ' + index + (index === trace.steps.length - 1 ? ' · FINAL' : '')), node('strong', frame.values.action || (index === trace.steps.length - 1 ? 'FINAL STATE' : 'STATE')));
    button.addEventListener('click', () => { state.step = index; renderTrace(); remember(); });
    $('timeline').append(button);
  }
  $('step-title').textContent = 'State ' + state.step;
  $('inspector').replaceChildren(table(artifact, state.step, artifact));
  $('comparison').replaceChildren(state.comparison ? table(state.comparison, state.step, artifact, true) : node('p', 'Choose another trace to compare the same step.', 'muted'));
  $('compare-title').textContent = state.comparison ? 'Comparison · revision ' + state.comparison.revision.slice(0, 8) : 'Comparison';
}
action('branch', async () => {
  if (!state.artifact?.validated) throw new Error('Replay validation is required before branching.');
  const constraint = $('branch-constraint').value.trim();
  await submit({operation: 'simulate', trace_id: state.artifact.id, prefix_length: state.step + 1,
    limits: {depth: number('branch-depth', 1, 10000)}, assumptions: constraint ? [constraint] : []});
});
action('export', () => {
  const blob = new Blob([JSON.stringify(state.artifact.trace, null, 2) + '\n'], {type: 'application/json'});
  const url = URL.createObjectURL(blob); const a = node('a'); a.href = url; a.download = 'trace-' + state.artifact.id.slice(0, 12) + '.json'; a.click(); setTimeout(() => URL.revokeObjectURL(url), 1000);
});
$('import').addEventListener('change', async () => {
  notice(null);
  try {
    ready(); const file = $('import').files[0]; if (!file) return;
    if (file.size > 16 * 1024 * 1024) throw new Error('Trace exceeds 16 MiB.');
    const trace = JSON.parse(await file.text());
    // Imported JSON is never rendered as HTML, and cannot enable export or branch.
    if (!trace || !Array.isArray(trace.steps) || trace.steps.some(s => !s || !s.values || typeof s.values !== 'object')) throw new Error('Invalid trace structure.');
    state.artifact = {trace, validated: false, revision: state.revision.id}; state.step = 0; renderTrace();
    state.importing = true; await submit({operation: 'validate-trace', trace});
  } catch (e) { notice(e); } finally { $('import').value = ''; }
});
function explanationOptions() {
  return {minimize: $('minimize').checked, checks: number('min-checks', 0, 1000000), wall_ms: number('min-ms', 0, 1000000)};
}
function assumptions() { return $('assumptions').value.split('\n').map(s => s.trim()).filter(Boolean); }
action('explain-init', () => submit({operation: 'explain-init', assumptions: assumptions(), explanation: explanationOptions()}));
action('explain-reach', () => submit({operation: 'explain-reach', target: $('target').value.trim(), limits: {depth: number('depth', 0, 10000)}, assumptions: assumptions(), explanation: explanationOptions()}));
action('explain-step', () => submit({operation: 'explain-step', trace_id: state.artifact.id, prefix_length: state.step + 1,
  assumptions: $('branch-constraint').value.trim() ? [$('branch-constraint').value.trim()] : [], explanation: explanationOptions()}));
function renderExplanation(job) {
  const explanation = job.result.explanation;
  if (!explanation) return;
  const container = $('explanation'); container.hidden = false; container.replaceChildren();
  container.append(node('h3', `Bound: ${explanation.bound} · ${explanation.scope.replaceAll('_', ' ')}`), node('p', explanation.background, 'muted'));
  const sources = new Map((job.result.constraints || []).map(c => [c.id, c]));
  const sourceLines = (id, visited = new Set()) => {
    if (visited.has(id)) return []; visited.add(id);
    const source = sources.get(id); if (!source) return [];
    return source.span?.line ? [source.span.line] : (source.parents || []).flatMap(p => sourceLines(p, visited));
  };
  for (const core of explanation.cases) {
    const details = node('details'); details.open = explanation.cases.length < 4;
    const label = core.subset_minimal ? 'subset-minimal' : 'nonminimal · ' + core.minimization.stop_reason;
    details.append(node('summary', `Depth ${core.depth} · ${core.constraints.length} conflicting constraints · ${label}`));
    const table = node('table'); const header = node('tr');
    for (const label of ['Kind / state', 'Constraint', 'Source']) header.append(node('th', label)); table.append(header);
    for (const constraint of core.constraints) {
      const row = node('tr'); row.append(node('td', `${constraint.kind} / ${constraint.step}`), node('td', constraint.expression));
      const location = node('td');
      const lines = [...new Set(constraint.source_ids.flatMap(id => sourceLines(id)))];
      for (const line of lines) {
        const link = node('button', 'Line ' + line, 'source-link'); link.disabled = state.dirty || state.revision?.id !== job.request.revision;
        link.addEventListener('click', () => {
          $('editor').open = true; $('source').focus();
          const text = $('source').value.split('\n'); const start = text.slice(0, line - 1).reduce((n, s) => n + s.length + 1, 0);
          $('source').setSelectionRange(start, start + (text[line - 1] || '').length); $('source').scrollIntoView({block: 'center'});
        }); location.append(link);
      }
      if (!lines.length) location.textContent = constraint.kind === 'pin' ? 'Pinned trace value' : constraint.kind === 'assumption' ? 'Query assumption' : constraint.kind === 'goal' ? 'Query goal' : 'Generated constraint';
      row.append(location); table.append(row);
    }
    details.append(table); container.append(details);
  }
}
async function refreshScenarios() {
  const scenarios = await api('scenarios');
  $('scenario').replaceChildren(option('Choose a scenario…', ''));
  for (const scenario of scenarios.filter(s => s.revision === state.revision?.id)) $('scenario').append(option(`${scenario.actions} actions · ${scenario.id.slice(0, 12)}`, scenario.id));
  $('scenario').value = state.scenario?.id || '';
  $('replay-scenario').disabled = !state.scenario || state.scenario.revision !== state.revision?.id;
  $('download-scenario').disabled = $('replay-scenario').disabled;
}
async function selectScenario(id) {
  state.scenario = id ? await api('scenarios/' + id) : null;
  $('scenario-detail').textContent = state.scenario ? `${state.scenario.actions.length} actions · Model trace validated at export · Adapter: ${state.scenario.adapter}. Implementation replay checks observations separately.` : 'Choose or export a scenario.';
  remember();
}
$('scenario').addEventListener('change', async () => { try { await selectScenario($('scenario').value); await refreshScenarios(); } catch (e) { notice(e); } });
action('export-scenario', () => submit({operation: 'export-scenario', trace_id: state.artifact.id}));
action('replay-scenario', () => submit({operation: 'replay-scenario', scenario_id: state.scenario.id, implementation: $('implementation').value}));
action('download-scenario', () => {
  const url = URL.createObjectURL(new Blob([JSON.stringify(state.scenario, null, 2) + '\n'], {type: 'application/json'}));
  const link = node('a'); link.href = url; link.download = 'scenario-' + state.scenario.id.slice(0, 12) + '.json'; link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
});
async function init() {
  state.examples = await api('examples');
  state.examples.forEach((example, index) => $('example').append(option(example.name, String(index))));
  let saved = {}; try { saved = JSON.parse(localStorage.getItem('yasmv-session') || '{}'); } catch (_) { /* Ignore obsolete local preferences. */ }
  await refreshRevisions();
  if (saved.revision) {
    try { await selectRevision(saved.revision); } catch (_) { /* A different store may be open. */ }
  } else if (state.examples.length) { $('example').value = '0'; fillEditor(state.examples[0]); markDirty(); }
  if (saved.trace) { try { await selectTrace(saved.trace); } catch (_) { /* Missing artifact. */ } }
  if (saved.comparison) { try { state.comparison = await api('traces/' + saved.comparison); } catch (_) { /* Missing artifact. */ } }
  state.step = Math.min(saved.step || 0, Math.max(0, (state.artifact?.trace.steps.length || 1) - 1));
  state.job = saved.job || null; lastPublished = state.job;
  if (saved.scenario) { try { await selectScenario(saved.scenario); } catch (_) {} }
  renderTrace(); await refreshTraces(); await refreshScenarios(); await refreshJobs(); remember();
  async function poll() { try { await refreshJobs(); } catch (e) { notice(e); } finally { setTimeout(poll, 700); } }
  setTimeout(poll, 700);
}
init().catch(notice);
