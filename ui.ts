// UI tests. Run `tsc && node ui` to run the tests in `tests/`

import fs from 'fs/promises';
import cp from 'child_process';
import { promisify } from 'util';

const exec = promisify(cp.exec);

let mode = process.argv.includes('--bless') ? 'bless' as const : 'check' as const;

function normalize(out: string): string {
    return out
        .replace(/^.+index\.js.+$/gm, '')
        .replace(/at .+/g, '')
        .replace(/^Node.js .+$/gm, '');
}

async function compareAndBlessFile(out: string, path: string, outKind: 'stdout' | 'stderr'): Promise<boolean> {
    let old: string;
    try {
        old = normalize(await fs.readFile(`${path}.${outKind}`, 'utf8'));
    } catch {
        old = '';
    }

    if (old !== out) {
        switch (mode) {
            case 'check': console.error(`${path} has wrong ${outKind}!`); break;
            case 'bless': await fs.writeFile(`${path}.${outKind}`, out);
        }
        return false;
    } else {
        return true;
    }
}

let pass = 0, fail = 0;
async function processDir(path: string) {
    const files = await fs.readdir(path);

    const work = files.map(async file => {
        if (file.endsWith('.stdout') || file.endsWith('.stderr')) return;
        let filePath = `${path}/${file}`;
        let stdout: string, stderr: string;
        try {
            const { stdout: out, stderr: err } = await exec(`node . ${filePath} --print-llir-only --no-timings --verbose --no-colors`);
            stdout = out;
            stderr = err;
        } catch (err: any) {
            stdout = err.stdout;
            stderr = err.stderr;
        }

        const [stdoutOk, stderrOk] = await Promise.all([
            compareAndBlessFile(normalize(stdout), filePath, 'stdout'),
            compareAndBlessFile(normalize(stderr), filePath, 'stderr')
        ]);
        if (stdoutOk && stderrOk) pass++;
        else fail++;
    });

    await Promise.all(work);
}

processDir('./tests').then(() => {
    console.log(`${pass} tests passed, ${fail} tests failed`);
    if (fail > 0) process.exit(1);
});

