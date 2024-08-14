import fs from 'fs';
import cProcess from 'child_process';
import { inspect as _inspect } from 'util';
import { options } from './cli';
import { parse } from './parse';
import { computeResolutions } from './resolve';
import { typeck } from './typeck';
import { addFileToSourceMap, createSourceMap, ppSpan } from './span';
import { ppTy } from './ty';
import { codegen } from './llvm';
import path from 'path';

function timed<T>(what: string, f: () => T): T {
    if (options.timings) {
        console.time(what);
        const res = f();
        console.timeEnd(what);
        return res;
    } else {
        return f();
    }
}

(function () {
    const sm = createSourceMap();
    const rootFile = addFileToSourceMap(sm, path.resolve(options.path), true);
    const ast = timed('parse', () => parse(sm, rootFile));
    const resolutions = timed('name res', () => computeResolutions(ast));
    // TODO: stop passing sm.source everywhere and properly hide it behind the sourcemap
    const tyres = timed('typeck', () => typeck(sm.source, ast, resolutions));
    if (options.verbose) {
        tyres.exprTys.forEach((v, k) => console.log(`expr @ ${ppSpan(sm.source, k.span)} => ${ppTy(v)}`));
        console.log();
    }
    if (tyres.hadErrors) {
        return;
    }
    const llir = timed('llir/mir codegen', () => codegen(sm.source, resolutions, tyres));

    if (options.printLlirOnly) {
        console.log(llir);
    } else {
        const llpath = `/tmp/tmpir${Date.now()}.ll`;
        fs.writeFileSync(llpath, llir);
        // TODO: don't use -Wno-override-module
        timed('clang', () => cProcess.spawnSync(`clang ${options.optLevel} -Wno-override-module ${llpath}`, {
            shell: true,
            stdio: 'inherit'
        }));
        fs.unlinkSync(llpath);
    }
})();
