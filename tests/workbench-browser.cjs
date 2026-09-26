/* M2 browser acceptance. Test-only dependency: Playwright with Chromium. */
const { chromium } = require(process.env.PLAYWRIGHT_MODULE || 'playwright');
const { spawn } = require('node:child_process');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const assert = require('node:assert/strict');

(async () => {
  const store = fs.mkdtempSync(path.join(os.tmpdir(), 'yasmv-browser-'));
  const server = spawn('python3', ['-m', 'tools.workbench', '--store', store, 'serve', '--port', '0'], {cwd: path.resolve(__dirname, '..'), stdio: ['ignore', 'ignore', 'pipe']});
  let browser;
  const errors = [];
  try {
    const base = await new Promise((resolve, reject) => {
      const timeout = setTimeout(() => reject(new Error('Server did not start')), 10000);
      server.stderr.on('data', chunk => {
        const match = chunk.toString().match(/http:\/\/127\.0\.0\.1:\d+/);
        if (match) { clearTimeout(timeout); resolve(match[0]); }
      });
      server.once('exit', code => { clearTimeout(timeout); reject(new Error('Server exited ' + code)); });
    });
    browser = await chromium.launch({headless: true});
    const page = await browser.newPage({viewport: {width: 1440, height: 1100}});
    page.on('pageerror', error => errors.push(error.message));
    await page.goto(base);
    await page.waitForFunction(() => document.querySelector('#source').value.includes('MODULE main'));
    const result = async text => {
      await page.waitForFunction(value => document.querySelector('#result-title').textContent.includes(value), text, {timeout: 90000});
    };
    await page.click('#save'); await result('Model validated');
    await page.click('#search'); await result('Goal reached at depth 5');
    await page.waitForSelector('.step:nth-child(6)');
    assert.equal(await page.locator('#trust').innerText(), 'Replay validated');
    await page.click('.step:nth-child(6)');
    assert.match(await page.locator('#inspector').innerText(), /Duplicate\s+true/);
    const original = await page.locator('#trace').inputValue();
    assert(original);
    const [download] = await Promise.all([page.waitForEvent('download'), page.click('#export')]);
    const traceFile = path.join(store, 'exported.json'); await download.saveAs(traceFile);
    const trace = JSON.parse(fs.readFileSync(traceFile));
    assert.equal(trace.steps.length, 6);
    await page.click('.step:nth-child(3)');
    await page.click('#branch-panel summary');
    await page.fill('#branch-depth', '3');
    await page.fill('#branch-constraint', 'action = DROP_ACK || action = RETRY || action = DELIVER');
    await page.click('#branch'); await result('Child trace created');
    await page.waitForFunction(old => document.querySelector('#trace').value && document.querySelector('#trace').value !== old, original);
    const child = await page.locator('#trace').inputValue();
    await page.selectOption('#compare', original);
    await page.waitForFunction(() => document.querySelector('#comparison table') !== null);
    await page.reload();
    await page.waitForFunction(expected => document.querySelector('#trace').value === expected, child);
    assert.equal(await page.locator('#compare').inputValue(), original);
    assert.equal(await page.locator('#trust').innerText(), 'Replay validated');
    // Changing a pinned action blocks the continuation without changing its parent.
    await page.selectOption('#trace', original);
    await page.waitForSelector('.step:nth-child(6)');
    await page.click('.step:nth-child(1)');
    await page.click('#branch-panel summary');
    await page.fill('#branch-constraint', 'action = ACK');
    await page.click('#branch'); await result('Continuation blocked');
    await page.waitForFunction(() => document.querySelectorAll('.step').length === 1);
    // Explain why the pinned SEND action cannot satisfy ACK.
    await page.selectOption('#trace', original);
    await page.waitForSelector('.step:nth-child(6)');
    await page.click('.step:nth-child(1)');
    await page.click('#explain-step'); await result('No valid next transition');
    await page.waitForSelector('#explanation:not([hidden])');
    assert.match(await page.locator('#explanation').innerText(), /subset-minimal/);
    assert.match(await page.locator('#explanation').innerText(), /Fixed model declarations/);
    assert.match(await page.locator('#explanation').innerText(), /action/);
    // Export the original witness and replay both implementations.
    await page.click('#export-scenario'); await result('Executable scenario exported');
    await page.waitForFunction(() => document.querySelector('#scenario').value.length > 0);
    const scenarioId = await page.locator('#scenario').inputValue();
    const [scenarioDownload] = await Promise.all([page.waitForEvent('download'), page.click('#download-scenario')]);
    const scenarioFile = path.join(store, 'scenario.json'); await scenarioDownload.saveAs(scenarioFile);
    assert.equal(JSON.parse(fs.readFileSync(scenarioFile)).actions.length, 5);
    await page.click('#replay-scenario'); await result('Implementation matched the scenario');
    assert.match(await page.locator('#result-detail').innerText(), /Duplicate execution reproduced/);
    await page.selectOption('#implementation', 'deduplicating');
    await page.click('#replay-scenario'); await result('Implementation diverged at step 5');
    assert.match(await page.locator('#replay-difference').innerText(), /executions/);
    await page.reload(); await result('Implementation diverged at step 5');
    await page.waitForFunction(expected => document.querySelector('#scenario').value === expected, scenarioId);
    // Import remains visibly untrusted until replay; a damaged valuation never becomes trusted.
    trace.steps[0].values.executions = '1';
    const damaged = path.join(store, 'damaged.json'); fs.writeFileSync(damaged, JSON.stringify(trace));
    await page.setInputFiles('#import', damaged);
    await page.waitForFunction(() => document.querySelector('#trust').textContent === 'Untrusted import');
    assert(await page.locator('#branch').isDisabled());
    await result('Trace failed replay');
    assert.equal(await page.locator('#trust').innerText(), 'Untrusted import');
    assert(await page.locator('#export').isDisabled());
    // Valid import recovers the original saved trace.
    await page.setInputFiles('#import', traceFile); await result('Trace passed replay');
    await page.waitForFunction(() => document.querySelector('#trust').textContent === 'Replay validated');
    // Cancel while the checker is still loading, then repeat successfully.
    await page.click('#search'); await page.waitForSelector('#cancel:not([hidden])');
    await page.click('#cancel'); await result('Inconclusive · cancelled');
    // Fixed model must label its bound, including after reload.
    await page.selectOption('#example', '1'); await page.click('#save'); await result('Model validated');
    await page.click('#search'); await result('No witness through depth 12');
    assert.match(await page.locator('#result-detail').innerText(), /not a safety proof/);
    await page.reload(); await result('No witness through depth 12');
    // Reopen the original immutable model and evidence.
    const revisions = await (await page.request.get(base + '/api/revisions')).json();
    const faulty = revisions.find(r => r.name === 'Faulty receiver');
    await page.selectOption('#revision', faulty.id);
    await page.selectOption('#trace', original);
    await page.waitForSelector('.step:nth-child(6)');
    await page.click('.step:nth-child(6)');
    assert.match(await page.locator('#inspector').innerText(), /Duplicate\s+true/);
    if (process.env.WORKBENCH_SCREENSHOT) await page.screenshot({path: process.env.WORKBENCH_SCREENSHOT, fullPage: true});
    await page.setViewportSize({width: 390, height: 844});
    assert(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth));
    assert.deepEqual(errors, []);
    console.log('Browser acceptance passed: load, validate, search, watches, export/import, selected-prefix branch, compare, reload, cancel, bounded negative, mobile layout, explanations, scenario export and implementation replay.');
  } finally {
    if (browser) await browser.close();
    server.kill('SIGTERM');
    await new Promise(resolve => server.exitCode !== null ? resolve() : server.once('exit', resolve));
    fs.rmSync(store, {recursive: true, force: true});
  }
})().catch(error => { console.error(error); process.exitCode = 1; });
